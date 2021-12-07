/*
 * Copyright (C) 2021 Aspeed Technology Inc.
 * Licensed under MPL 2.0 (see LICENSE.txt)
 *
 */
#include "emscripten.h"
#include "jtable.h"

//#define pr_dbg(fmt, args...) printf("%s(): " fmt, __func__, ## args)
#define pr_dbg(fmt, args...)

#define ALIGN(x,a)      (((x)+(a)-1)&~(a-1))
#define MIN(a,b)        (((a)<(b))?(a):(b))
#define MAKEWORD(a,b)   ((WORD)(((BYTE)(a))|(((WORD)((BYTE)(b)))<<8)))

// block header
#define BLOCK_HEADER_MASK 0x0F
#define JPEG_NO_SKIP_CODE 0x00
#define LOW_JPEG_NO_SKIP_CODE 0x04
#define LOW_JPEG_SKIP_CODE 0x0C
#define JPEG_SKIP_CODE 0x08
#define FRAME_END_CODE 0x09
#define JPEG_PASS2_CODE 0x02
#define JPEG_SKIP_PASS2_CODE 0x0A

// block length
#define BLOCK_AST2100_START_LENGTH 0x04
#define BLOCK_AST2100_SKIP_LENGTH 20 // S:1 H:3 X:8 Y:8

struct RGB {
    BYTE R;
    BYTE G;
    BYTE B;
    BYTE Reserved;
};
struct YUV {
    BYTE Y;
    BYTE U;
    BYTE V;
};

static long QT[4][64]; // quantization tables, no more than 4 quantization tables (QT[0..3])
static int Cr2R_tbl[256], Cb2B_tbl[256], Cr2G_tbl[256], Cb2G_tbl[256], Y_tbl[256];
static BYTE* rlimit_tbl;
static Huffman_table HTDC[4]; //DC huffman tables , no more than 4 (0..3)
static Huffman_table HTAC[4]; //AC huffman tables                  (0..3)

static BYTE YDC_nr = 0, CbDC_nr = 1, CrDC_nr = 1; // DC Huffman table number for Y,Cb, Cr
static BYTE YAC_nr = 0, CbAC_nr = 1, CrAC_nr = 1; // AC Huffman table number for Y,Cb, Cr

static SHORT DCY, DCCb, DCCr;  // Coeficientii DC pentru Y,Cb,Cr
static SHORT DCT_coeff[384];   // Current DCT_coefficients
static BYTE block_buf[768]; // temporary yuv buffer for each block
static struct YUV* yuv_buf;    // yuv buffer of whole frame For Pass2

// compression parameters
static unsigned char selector, advance_selector;
static unsigned char mode420;

static int SCALEFACTOR = 16, SCALEFACTORUV = 16;
static int ADVANCESCALEFACTOR = 16, ADVANCESCALEFACTORUV = 16;
static int Mapping = 0;

static unsigned char first_frame = 1;

// input compressed data
static unsigned long* in_buf;
static unsigned long in_buf_index;

// how many bits of 32-bit data pointed by 'in_buf_index' is not skipped yet
static int newbits;
// current/next 32-bit input data
static unsigned long cur_data, next_data;

// the position in the image
//  unit: macro block
static int mbwidth, mbheight;

// compressed image's width, height
static unsigned int height, width;

static void InitBuffer()
{
    //For 2Pass
    yuv_buf = malloc((size_t)1920 * 1200 * 3);
}

static void InitColorTable()
{
    int i, x;
    int nHalf = (1L << 16) >> 1;

#define FIX(x) ((int)((x)*(1L << 16) + 0.5))

    /* i is the actual input pixel value, in the range 0..MAXJSAMPLE */
    /* The Cb or Cr value we are thinking of is x = i - CENTERJSAMPLE */
    /* Cr=>R value is nearest int to 1.597656 * x */
    /* Cb=>B value is nearest int to 2.015625 * x */
    /* Cr=>G value is scaled-up -0.8125 * x */
    /* Cb=>G value is scaled-up -0.390625 * x */
    for (i = 0, x = -128; i < 256; i++, x++) {
        Cr2R_tbl[i] = (int)(FIX(1.597656) * x + nHalf) >> 16;
        Cb2B_tbl[i] = (int)(FIX(2.015625) * x + nHalf) >> 16;
        Cr2G_tbl[i] = (int)(-FIX(0.8125) * x + nHalf) >> 16;
        Cb2G_tbl[i] = (int)(-FIX(0.390625) * x + nHalf) >> 16;
    }
    for (i = 0, x = -16; i < 256; i++, x++) {
        Y_tbl[i] = (int)(FIX(1.164) * x + nHalf) >> 16;
    }
}

/* Allocate and fill in the sample_range_limit table */
static void InitRangeLimitTable()
{
    int j;
    rlimit_tbl = (BYTE*)malloc(5 * 256L + 128);
    /* First segment of "simple" table: limit[x] = 0 for x < 0 */
    memset((void*)rlimit_tbl, 0, 256);
    rlimit_tbl += 256; /* allow negative subscripts of simple table */
    /* Main part of "simple" table: limit[x] = x */
    for (j = 0; j < 256; j++)
        rlimit_tbl[j] = j;
    /* End of simple table, rest of first half of post-IDCT table */
    memset((void*)(rlimit_tbl + 256), 255, 384);

    /* Second half of post-IDCT table */
    memset((void*)(rlimit_tbl + 640), 0, 384);
    for (j = 0; j < 128; j++)
        rlimit_tbl[j + 1024] = j;
}

static void LoadHuffmanTable(Huffman_table* HT, BYTE* nrcode, BYTE* value, WORD* Huff_code)
{
    BYTE k, j, i;
    DWORD code, code_index;

    for (j = 1; j <= 16; j++) {
        HT->Length[j] = nrcode[j];
    }

    for (i = 0, k = 1; k <= 16; k++)
        for (j = 0; j < HT->Length[k]; j++) {
            HT->V[MAKEWORD(k, j)] = value[i];
            i++;
        }

    code = 0;
    for (k = 1; k <= 16; k++) {
        HT->minor_code[k] = (WORD)code;
        for (j = 1; j <= HT->Length[k]; j++)
            code++;
        HT->major_code[k] = (WORD)(code - 1);
        code *= 2;
        if (HT->Length[k] == 0) {
            HT->minor_code[k] = 0xFFFF;
            HT->major_code[k] = 0;
        }
    }

    HT->Len[0] = 2;
    i = 2;

    for (code_index = 1; code_index < 65536; code_index++) {
        if (code_index >= Huff_code[i])
            i += 2;
        HT->Len[code_index] = (unsigned char)Huff_code[i + 1];
    }
}

// setup all table needed
static void InitTable()
{
    InitColorTable();
    InitRangeLimitTable();
    LoadHuffmanTable(&HTDC[0], std_dc_luminance_nrcodes, std_dc_luminance_values, DC_LUMINANCE_HUFFMANCODE);
    LoadHuffmanTable(&HTAC[0], std_ac_luminance_nrcodes, std_ac_luminance_values, AC_LUMINANCE_HUFFMANCODE);
    LoadHuffmanTable(&HTDC[1], std_dc_chrominance_nrcodes, std_dc_chrominance_values, DC_CHROMINANCE_HUFFMANCODE);
    LoadHuffmanTable(&HTAC[1], std_ac_chrominance_nrcodes, std_ac_chrominance_values, AC_CHROMINANCE_HUFFMANCODE);
}

// Set quantization table and zigzag reorder it
static void set_quant_table(BYTE* basic_table, BYTE scale_factor, long* newtable)
{
    BYTE i;
    long temp;

    for (i = 0; i < 64; i++) {
        temp = ((long)(basic_table[i] * 16) / scale_factor);
        /* limit the values to the valid range */
        if (temp <= 0L)
            temp = 1L;
        if (temp > 255L)
            temp = 255L; /* limit to baseline range if requested */
        newtable[i] = (BYTE)temp;
    }
}

static void load_quant_table(long* quant_table)
{
    float scalefactor[8] = { 1.0f, 1.387039845f, 1.306562965f, 1.175875602f,
                             1.0f, 0.785694958f, 0.541196100f, 0.275899379f };
    BYTE j = 0, row, col;
    BYTE *std_luminance_qt;

    // Load quantization coefficients from JPG file, scale them for DCT and reorder
    // from zig-zag order
    switch (selector) {
    case 0:
        std_luminance_qt = Tbl_000Y;
        break;
    case 1:
        std_luminance_qt = Tbl_014Y;
        break;
    case 2:
        std_luminance_qt = Tbl_029Y;
        break;
    case 3:
        std_luminance_qt = Tbl_043Y;
        break;
    case 4:
        std_luminance_qt = Tbl_057Y;
        break;
    case 5:
        std_luminance_qt = Tbl_071Y;
        break;
    case 6:
        std_luminance_qt = Tbl_086Y;
        break;
    case 7:
        std_luminance_qt = Tbl_100Y;
        break;
    case 8:
        std_luminance_qt = Tbl_08Y;
        break;
    case 9:
        std_luminance_qt = Tbl_09Y;
        break;
    case 10:
        std_luminance_qt = Tbl_10Y;
        break;
    case 11:
        std_luminance_qt = Tbl_11Y;
        break;
    }
    set_quant_table(std_luminance_qt, (BYTE)SCALEFACTOR, quant_table);

    for (row = 0; row < 8; row++)
        for (col = 0; col < 8; col++) {
            quant_table[j] = (long)((quant_table[j] * scalefactor[row] * scalefactor[col]) * 65536);
            j++;
        }
}

static void load_quant_tableCb(long* quant_table)
{
    float scalefactor[8] = { 1.0f, 1.387039845f, 1.306562965f, 1.175875602f,
                             1.0f, 0.785694958f, 0.541196100f, 0.275899379f };
    BYTE j = 0, row, col;
    BYTE *std_chrominance_qt;

    // Load quantization coefficients from JPG file, scale them for DCT and reorder
    // from zig-zag order
    if (Mapping == 1) {
        switch (selector) {
        case 0:
            std_chrominance_qt = Tbl_000Y;
            break;
        case 1:
            std_chrominance_qt = Tbl_014Y;
            break;
        case 2:
            std_chrominance_qt = Tbl_029Y;
            break;
        case 3:
            std_chrominance_qt = Tbl_043Y;
            break;
        case 4:
            std_chrominance_qt = Tbl_057Y;
            break;
        case 5:
            std_chrominance_qt = Tbl_071Y;
            break;
        case 6:
            std_chrominance_qt = Tbl_086Y;
            break;
        case 7:
            std_chrominance_qt = Tbl_100Y;
            break;
        case 8:
            std_chrominance_qt = Tbl_08Y;
            break;
        case 9:
            std_chrominance_qt = Tbl_09Y;
            break;
        case 10:
            std_chrominance_qt = Tbl_10Y;
            break;
        case 11:
            std_chrominance_qt = Tbl_11Y;
            break;
        }
    } else {
        switch (selector) {
        case 0:
            std_chrominance_qt = Tbl_000UV;
            break;
        case 1:
            std_chrominance_qt = Tbl_014UV;
            break;
        case 2:
            std_chrominance_qt = Tbl_029UV;
            break;
        case 3:
            std_chrominance_qt = Tbl_043UV;
            break;
        case 4:
            std_chrominance_qt = Tbl_057UV;
            break;
        case 5:
            std_chrominance_qt = Tbl_071UV;
            break;
        case 6:
            std_chrominance_qt = Tbl_086UV;
            break;
        case 7:
            std_chrominance_qt = Tbl_100UV;
            break;
        case 8:
            std_chrominance_qt = Tbl_08UV;
            break;
        case 9:
            std_chrominance_qt = Tbl_09UV;
            break;
        case 10:
            std_chrominance_qt = Tbl_10UV;
            break;
        case 11:
            std_chrominance_qt = Tbl_11UV;
            break;
        }
    }
    set_quant_table(std_chrominance_qt, (BYTE)SCALEFACTORUV, quant_table);

    for (row = 0; row < 8; row++)
        for (col = 0; col < 8; col++) {
            quant_table[j] = (long)((quant_table[j] * scalefactor[row] * scalefactor[col]) * 65536);
            j++;
        }
}

//  Note: Added for Dual_JPEG
static void load_advance_quant_table(long* quant_table)
{
    float scalefactor[8] = { 1.0f, 1.387039845f, 1.306562965f, 1.175875602f,
                             1.0f, 0.785694958f, 0.541196100f, 0.275899379f };
    BYTE j = 0, row, col;
    BYTE *std_luminance_qt;

    // Load quantization coefficients from JPG file, scale them for DCT and reorder
    // from zig-zag order
    switch (advance_selector) {
    case 0:
        std_luminance_qt = Tbl_000Y;
        break;
    case 1:
        std_luminance_qt = Tbl_014Y;
        break;
    case 2:
        std_luminance_qt = Tbl_029Y;
        break;
    case 3:
        std_luminance_qt = Tbl_043Y;
        break;
    case 4:
        std_luminance_qt = Tbl_057Y;
        break;
    case 5:
        std_luminance_qt = Tbl_071Y;
        break;
    case 6:
        std_luminance_qt = Tbl_086Y;
        break;
    case 7:
        std_luminance_qt = Tbl_100Y;
        break;
    case 8:
        std_luminance_qt = Tbl_08Y;
        break;
    case 9:
        std_luminance_qt = Tbl_09Y;
        break;
    case 10:
        std_luminance_qt = Tbl_10Y;
        break;
    case 11:
        std_luminance_qt = Tbl_11Y;
        break;
    }
    //  Note: pass ADVANCE SCALE FACTOR to sub-function in Dual-JPEG
    set_quant_table(std_luminance_qt, (BYTE)ADVANCESCALEFACTOR, quant_table);

    for (row = 0; row < 8; row++)
        for (col = 0; col < 8; col++) {
            quant_table[j] = (long)((quant_table[j] * scalefactor[row] * scalefactor[col]) * 65536);
            j++;
        }
}

//  Note: Added for Dual-JPEG
static void load_advance_quant_tableCb(long* quant_table)
{
    float scalefactor[8] = { 1.0f, 1.387039845f, 1.306562965f, 1.175875602f,
                             1.0f, 0.785694958f, 0.541196100f, 0.275899379f };
    BYTE j = 0, row, col;
    BYTE *std_chrominance_qt;

    // Load quantization coefficients from JPG file, scale them for DCT and reorder
    // from zig-zag order
    if (Mapping == 1) {
        switch (advance_selector) {
        case 0:
            std_chrominance_qt = Tbl_000Y;
            break;
        case 1:
            std_chrominance_qt = Tbl_014Y;
            break;
        case 2:
            std_chrominance_qt = Tbl_029Y;
            break;
        case 3:
            std_chrominance_qt = Tbl_043Y;
            break;
        case 4:
            std_chrominance_qt = Tbl_057Y;
            break;
        case 5:
            std_chrominance_qt = Tbl_071Y;
            break;
        case 6:
            std_chrominance_qt = Tbl_086Y;
            break;
        case 7:
            std_chrominance_qt = Tbl_100Y;
            break;
        case 8:
            std_chrominance_qt = Tbl_08Y;
            break;
        case 9:
            std_chrominance_qt = Tbl_09Y;
            break;
        case 10:
            std_chrominance_qt = Tbl_10Y;
            break;
        case 11:
            std_chrominance_qt = Tbl_11Y;
            break;
        }
    } else {
        switch (advance_selector) {
        case 0:
            std_chrominance_qt = Tbl_000UV;
            break;
        case 1:
            std_chrominance_qt = Tbl_014UV;
            break;
        case 2:
            std_chrominance_qt = Tbl_029UV;
            break;
        case 3:
            std_chrominance_qt = Tbl_043UV;
            break;
        case 4:
            std_chrominance_qt = Tbl_057UV;
            break;
        case 5:
            std_chrominance_qt = Tbl_071UV;
            break;
        case 6:
            std_chrominance_qt = Tbl_086UV;
            break;
        case 7:
            std_chrominance_qt = Tbl_100UV;
            break;
        case 8:
            std_chrominance_qt = Tbl_08UV;
            break;
        case 9:
            std_chrominance_qt = Tbl_09UV;
            break;
        case 10:
            std_chrominance_qt = Tbl_10UV;
            break;
        case 11:
            std_chrominance_qt = Tbl_11UV;
            break;
        }
    }
    //  Note: pass ADVANCE SCALE FACTOR to sub-function in Dual-JPEG
    set_quant_table(std_chrominance_qt, (BYTE)ADVANCESCALEFACTORUV, quant_table);

    for (row = 0; row < 8; row++)
        for (col = 0; col < 8; col++) {
            quant_table[j] = (long)((quant_table[j] * scalefactor[row] * scalefactor[col]) * 65536);
            j++;
        }
}

static WORD ShowBits(BYTE bits)
{
    return (WORD)(cur_data >> (32 - bits));
}

static void SkipBits(BYTE bits)
{
    if (newbits <= bits) {
        unsigned long data = in_buf[in_buf_index++];

        cur_data = (cur_data << bits) | ((next_data | (data >> (newbits))) >> (32 - bits));
        next_data = data << (bits - newbits);
        newbits = 32 + newbits - bits;
    } else {
        cur_data = (cur_data << bits) | (next_data >> (32 - bits));
        next_data = next_data << bits;
        newbits -= bits;
    }
}

static SHORT GetBits(BYTE bits)
{
    static SHORT neg_pow2[17] = { 0, -1, -3, -7, -15, -31, -63, -127, -255, -511, -1023, -2047, -4095, -8191, -16383, -32767 };
    SHORT signed_wordvalue;

    signed_wordvalue = ShowBits(bits);
    if (((1L << (bits - 1)) & signed_wordvalue) == 0)
        signed_wordvalue += neg_pow2[bits];

    SkipBits(bits);
    return signed_wordvalue;
}

static void YUVToRGB(
    int mbx, int mby,
    unsigned char* pYCbCr, //in, Y: 256 or 64 bytes; Cb: 64 bytes; Cr: 64 bytes
    struct YUV* pYUV, //in, Y: 256 or 64 bytes; Cb: 64 bytes; Cr: 64 bytes
    unsigned char* pBgr //out, BGR format, 16*16*3 = 768 bytes; or 8*8*3=192 bytes
)
{
    int i, j, pos, m, n;
    unsigned char cb, cr, *py, *pcb, *pcr, *py420[4];
    int y;
    struct RGB* pByte = (struct RGB*)pBgr;
    WORD pixel_x, pixel_y;
    WORD tmp_x, tmp_y;

    if (mode420 == 0) {
        py = pYCbCr;
        pcb = pYCbCr + 64;
        pcr = pcb + 64;

        pixel_x = mbx << 3;
        pixel_y = mby << 3;
        pos = (pixel_y * width) + pixel_x;
        tmp_x = MIN(width - pixel_x, 8);
        tmp_y = MIN(height - pixel_y, 8);

        for (j = 0; j < tmp_y; j++) {
            for (i = 0; i < tmp_x; i++) {
                m = ((j << 3) + i);
                y = py[m];
                cb = pcb[m];
                cr = pcr[m];
                n = pos + i;
                //For 2Pass. Save the YUV value
                pYUV[n].Y = y;
                pYUV[n].U = cb;
                pYUV[n].V = cr;
                pByte[n].B = rlimit_tbl[Y_tbl[y] + Cb2B_tbl[cb]];
                pByte[n].G = rlimit_tbl[Y_tbl[y] + Cb2G_tbl[cb] + Cr2G_tbl[cr]];
                pByte[n].R = rlimit_tbl[Y_tbl[y] + Cr2R_tbl[cr]];
            }
            pos += width;
        }
    } else {
        for (i = 0; i < 4; i++)
            py420[i] = pYCbCr + i * 64;
        pcb = pYCbCr + 4 * 64;
        pcr = pcb + 64;

        pixel_x = mbx << 4;
        pixel_y = mby << 4;
        pos = (pixel_y * width) + pixel_x;
        tmp_x = MIN(width - pixel_x, 16);
        tmp_y = MIN(height - pixel_y, 16);

        for (j = 0; j < tmp_y; j++) {
            for (i = 0; i < tmp_x; i++) {
                y = *(py420[(j >> 3) * 2 + (i >> 3)]++);
                m = ((j >> 1) << 3) + (i >> 1);
                cb = pcb[m];
                cr = pcr[m];
                n = pos + i;
                pByte[n].B = rlimit_tbl[Y_tbl[y] + Cb2B_tbl[cb]];
                pByte[n].G = rlimit_tbl[Y_tbl[y] + Cb2G_tbl[cb] + Cr2G_tbl[cr]];
                pByte[n].R = rlimit_tbl[Y_tbl[y] + Cr2R_tbl[cr]];
            }
            pos += width;
        }
    }
}

static void YUVToRGBPass2(
    int mbx, int mby,
    unsigned char* pYCbCr, //in, Y: 256 or 64 bytes; Cb: 64 bytes; Cr: 64 bytes
    struct YUV* pYUV, //out, BGR format, 16*16*3 = 768 bytes; or 8*8*3=192 bytes
    unsigned char* pBgr //out, BGR format, 16*16*3 = 768 bytes; or 8*8*3=192 bytes
)
{
    int i, j, pos, m, n;
    unsigned char cb, cr, *py, *pcb, *pcr;
    int y;
    struct RGB* pByte = (struct RGB*)pBgr;
    WORD pixel_x, pixel_y;
    WORD tmp_x, tmp_y;

    if (mode420) {
        pr_dbg("pass2 not supported in yuv420\n");
        return;
    }

    py = pYCbCr;
    pcb = pYCbCr + 64;
    pcr = pcb + 64;

    pixel_x = mbx * 8;
    pixel_y = mby * 8;
    pos = (pixel_y * width) + pixel_x;
    tmp_x = MIN(width - pixel_x, 8);
    tmp_y = MIN(height - pixel_y, 8);

    for (j = 0; j < tmp_y; j++) {
        for (i = 0; i < tmp_x; i++) {
            m = ((j << 3) + i);
            n = pos + i;
            y = (pYUV[n].Y += (py[m] - 128));
            cb = (pYUV[n].U += (pcb[m] - 128));
            cr = (pYUV[n].V += (pcr[m] - 128));
            pByte[n].B = rlimit_tbl[Y_tbl[y] + Cb2B_tbl[cb]];
            pByte[n].G = rlimit_tbl[Y_tbl[y] + Cb2G_tbl[cb] + Cr2G_tbl[cr]];
            pByte[n].R = rlimit_tbl[Y_tbl[y] + Cr2R_tbl[cr]];
        }
        pos += width;
    }
}

// baseline
static void DecodeHuffmanDataUnit(BYTE DC_nr, BYTE AC_nr, SHORT* previous_DC, WORD pos)
{
    BYTE nr, k;
    WORD tmp_Hcode;
    BYTE size_val, count_0;
    WORD* min_code;
    BYTE* huff_values;
    BYTE tmp;

    min_code = HTDC[DC_nr].minor_code;
    huff_values = HTDC[DC_nr].V;

    // 1st phase, DC coefficient
    nr = 0;
    k = HTDC[DC_nr].Len[(WORD)(cur_data >> 16)];
    tmp_Hcode = ShowBits(k);
    SkipBits(k);
    size_val = huff_values[MAKEWORD(k, (BYTE)(tmp_Hcode - min_code[k]))];
    if (size_val == 0)
        DCT_coeff[pos + 0] = *previous_DC;
    else
        DCT_coeff[pos + 0] = (*previous_DC += GetBits(size_val));

    // 2nd phase, AC coefficient
    min_code = HTAC[AC_nr].minor_code;
    huff_values = HTAC[AC_nr].V;

    nr = 1; // AC coefficient
    do {
        k = HTAC[AC_nr].Len[(WORD)(cur_data >> 16)];
        tmp_Hcode = ShowBits(k);
        SkipBits(k);

        tmp = huff_values[MAKEWORD(k, (BYTE)(tmp_Hcode - min_code[k]))];
        size_val = tmp & 0xF;
        count_0 = tmp >> 4;
        if (size_val == 0) {
            if (count_0 != 0xF)
                break;
            nr += 16;
        } else {
            nr += count_0; //skip count_0 zeroes
            DCT_coeff[pos + dezigzag[nr++]] = GetBits(size_val);
        }
    } while (nr < 64);
}

// dequant & IDCT
static void InverseDCT(short* coef, BYTE* data, BYTE nBlock)
{
#define FIX_1_082392200 ((int)277)
#define FIX_1_414213562 ((int)362)
#define FIX_1_847759065 ((int)473)
#define FIX_2_613125930 ((int)669)

#define MULTIPLY(var, cons) ((int)((var) * (cons)) >> 8)
#define DCTSIZE 8

    int tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    int tmp10, tmp11, tmp12, tmp13;
    int z5, z10, z11, z12, z13;
    int workspace[64]; /* buffers data between passes */

    short* inptr = coef;
    long* quantptr = QT[nBlock];
    int* wsptr = workspace;
    unsigned char* outptr;
    unsigned char* r_limit = rlimit_tbl + 128;
    int i;


    //Pass 1: process columns from input (inptr), store into work array(wsptr)
    for (i = 8; i > 0; i--) {
        /* Due to quantization, we will usually find that many of the input
	* coefficients are zero, especially the AC terms.  We can exploit this
	* by short-circuiting the IDCT calculation for any column in which all
	* the AC terms are zero.  In that case each output is equal to the
	* DC coefficient (with scale factor as needed).
	* With typical images and quantization tables, half or more of the
	* column DCT calculations can be simplified this way.
	*/

        /* check for AC terms all zero */
        if (inptr[DCTSIZE * 1] == 0 && inptr[DCTSIZE * 2] == 0 &&
            inptr[DCTSIZE * 3] == 0 && inptr[DCTSIZE * 4] == 0 &&
            inptr[DCTSIZE * 5] == 0 && inptr[DCTSIZE * 6] == 0 &&
            inptr[DCTSIZE * 7]) {
            wsptr[DCTSIZE * 0] = wsptr[DCTSIZE * 1] = wsptr[DCTSIZE * 2] =
                                 wsptr[DCTSIZE * 3] = wsptr[DCTSIZE * 4] =
                                 wsptr[DCTSIZE * 5] = wsptr[DCTSIZE * 6] =
                                 wsptr[DCTSIZE * 7] =
                                 (inptr[DCTSIZE * 0] * quantptr[DCTSIZE * 0]) >> 16;

            inptr++; /* advance pointers to next column */
            quantptr++;
            wsptr++;
            continue;
        }

        /* Even part */

        tmp0 = (inptr[DCTSIZE * 0] * quantptr[DCTSIZE * 0]) >> 16;
        tmp1 = (inptr[DCTSIZE * 2] * quantptr[DCTSIZE * 2]) >> 16;
        tmp2 = (inptr[DCTSIZE * 4] * quantptr[DCTSIZE * 4]) >> 16;
        tmp3 = (inptr[DCTSIZE * 6] * quantptr[DCTSIZE * 6]) >> 16;

        tmp10 = tmp0 + tmp2; /* phase 3 */
        tmp11 = tmp0 - tmp2;

        tmp13 = tmp1 + tmp3; /* phases 5-3 */
        tmp12 = MULTIPLY(tmp1 - tmp3, FIX_1_414213562) - tmp13; /* 2*c4 */

        tmp0 = tmp10 + tmp13; /* phase 2 */
        tmp3 = tmp10 - tmp13;
        tmp1 = tmp11 + tmp12;
        tmp2 = tmp11 - tmp12;

        /* Odd part */

        tmp4 = (inptr[DCTSIZE * 1] * quantptr[DCTSIZE * 1]) >> 16;
        tmp5 = (inptr[DCTSIZE * 3] * quantptr[DCTSIZE * 3]) >> 16;
        tmp6 = (inptr[DCTSIZE * 5] * quantptr[DCTSIZE * 5]) >> 16;
        tmp7 = (inptr[DCTSIZE * 7] * quantptr[DCTSIZE * 7]) >> 16;

        z13 = tmp6 + tmp5; /* phase 6 */
        z10 = tmp6 - tmp5;
        z11 = tmp4 + tmp7;
        z12 = tmp4 - tmp7;

        tmp7 = z11 + z13; /* phase 5 */
        tmp11 = MULTIPLY(z11 - z13, FIX_1_414213562); /* 2*c4 */

        z5 = MULTIPLY(z10 + z12, FIX_1_847759065); /* 2*c2 */
        tmp10 = MULTIPLY(z12, FIX_1_082392200) - z5; /* 2*(c2-c6) */
        tmp12 = MULTIPLY(z10, -FIX_2_613125930) + z5; /* -2*(c2+c6) */

        tmp6 = tmp12 - tmp7; /* phase 2 */
        tmp5 = tmp11 - tmp6;
        tmp4 = tmp10 + tmp5;

        wsptr[DCTSIZE * 0] = (tmp0 + tmp7);
        wsptr[DCTSIZE * 7] = (tmp0 - tmp7);
        wsptr[DCTSIZE * 1] = (tmp1 + tmp6);
        wsptr[DCTSIZE * 6] = (tmp1 - tmp6);
        wsptr[DCTSIZE * 2] = (tmp2 + tmp5);
        wsptr[DCTSIZE * 5] = (tmp2 - tmp5);
        wsptr[DCTSIZE * 4] = (tmp3 + tmp4);
        wsptr[DCTSIZE * 3] = (tmp3 - tmp4);

        inptr++; /* advance pointers to next column */
        quantptr++;
        wsptr++;
    }

    /* Pass 2: process rows from work array, store into output array. */
    /* Note that we must descale the results by a factor of 8 == 2**3, */
    /* and also undo the PASS1_BITS scaling. */

//#define RANGE_MASK 1023; //2 bits wider than legal samples
#define PASS1_BITS 0
#define IDESCALE(x, n) ((int)((x) >> n))

    wsptr = workspace;
    for (i = 0; i < DCTSIZE; i++) {
        outptr = data + (i << 3);

        /* check for AC terms all zero */
        if (wsptr[1] == 0 && wsptr[2] == 0 &&
            wsptr[3] == 0 && wsptr[4] == 0 &&
            wsptr[5] == 0 && wsptr[6] == 0 &&
            wsptr[7] == 0) {
            /* AC terms all zero */

            outptr[0] = outptr[1] = outptr[2] = outptr[3] = outptr[4] =
                        outptr[5] = outptr[6] = outptr[7] =
                        r_limit[IDESCALE(wsptr[0], (PASS1_BITS + 3)) & 1023L];

            wsptr += DCTSIZE; /* advance pointer to next row */
            continue;
        }
        /* Even part */

        tmp10 = (wsptr[0] + wsptr[4]);
        tmp11 = (wsptr[0] - wsptr[4]);

        tmp13 = (wsptr[2] + wsptr[6]);
        tmp12 = MULTIPLY(wsptr[2] - wsptr[6], FIX_1_414213562) - tmp13;

        tmp0 = tmp10 + tmp13;
        tmp3 = tmp10 - tmp13;
        tmp1 = tmp11 + tmp12;
        tmp2 = tmp11 - tmp12;

        /* Odd part */

        z13 = wsptr[5] + wsptr[3];
        z10 = wsptr[5] - wsptr[3];
        z11 = wsptr[1] + wsptr[7];
        z12 = wsptr[1] - wsptr[7];

        tmp7 = z11 + z13; /* phase 5 */
        tmp11 = MULTIPLY(z11 - z13, FIX_1_414213562); /* 2*c4 */

        z5 = MULTIPLY(z10 + z12, FIX_1_847759065); /* 2*c2 */
        tmp10 = MULTIPLY(z12, FIX_1_082392200) - z5; /* 2*(c2-c6) */
        tmp12 = MULTIPLY(z10, -FIX_2_613125930) + z5; /* -2*(c2+c6) */

        tmp6 = tmp12 - tmp7; /* phase 2 */
        tmp5 = tmp11 - tmp6;
        tmp4 = tmp10 + tmp5;

        /* Final output stage: scale down by a factor of 8 and range-limit */
        outptr[0] = r_limit[IDESCALE((tmp0 + tmp7), (PASS1_BITS + 3)) & 1023L];
        outptr[7] = r_limit[IDESCALE((tmp0 - tmp7), (PASS1_BITS + 3)) & 1023L];
        outptr[1] = r_limit[IDESCALE((tmp1 + tmp6), (PASS1_BITS + 3)) & 1023L];
        outptr[6] = r_limit[IDESCALE((tmp1 - tmp6), (PASS1_BITS + 3)) & 1023L];
        outptr[2] = r_limit[IDESCALE((tmp2 + tmp5), (PASS1_BITS + 3)) & 1023L];
        outptr[5] = r_limit[IDESCALE((tmp2 - tmp5), (PASS1_BITS + 3)) & 1023L];
        outptr[4] = r_limit[IDESCALE((tmp3 + tmp4), (PASS1_BITS + 3)) & 1023L];
        outptr[3] = r_limit[IDESCALE((tmp3 - tmp4), (PASS1_BITS + 3)) & 1023L];

        wsptr += DCTSIZE; /* advance pointer to next row */
    }
}

static int Decompress(int mbx, int mby, unsigned char* out_buf, BYTE QT_TableSelection)
{
    unsigned char* ptr;

    memset(DCT_coeff, 0, sizeof(DCT_coeff[0]) * 192 * (1 + mode420));

    ptr = block_buf;
    if (mode420) {
        DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 0);
        InverseDCT(DCT_coeff, ptr, QT_TableSelection);
        ptr += 64;

        DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 64);
        InverseDCT(DCT_coeff + 64, ptr, QT_TableSelection);
        ptr += 64;

        DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 128);
        InverseDCT(DCT_coeff + 128, ptr, QT_TableSelection);
        ptr += 64;

        DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 192);
        InverseDCT(DCT_coeff + 192, ptr, QT_TableSelection);
        ptr += 64;

        DecodeHuffmanDataUnit(CbDC_nr, CbAC_nr, &DCCb, 256);
        InverseDCT(DCT_coeff + 256, ptr, QT_TableSelection + 1);
        ptr += 64;

        DecodeHuffmanDataUnit(CrDC_nr, CrAC_nr, &DCCr, 320);
        InverseDCT(DCT_coeff + 320, ptr, QT_TableSelection + 1);
    } else {
        DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 0);
        InverseDCT(DCT_coeff, ptr, QT_TableSelection);
        ptr += 64;

        DecodeHuffmanDataUnit(CbDC_nr, CbAC_nr, &DCCb, 64);
        InverseDCT(DCT_coeff + 64, ptr, QT_TableSelection + 1);
        ptr += 64;

        DecodeHuffmanDataUnit(CrDC_nr, CrAC_nr, &DCCr, 128);
        InverseDCT(DCT_coeff + 128, ptr, QT_TableSelection + 1);
    }

    YUVToRGB(mbx, mby, block_buf, yuv_buf, out_buf);

    return 0;
}

static int DecompressPASS2(int mbx, int mby, unsigned char* out_buf, BYTE QT_TableSelection)
{
    unsigned char* ptr;

    memset(DCT_coeff, 0, sizeof(DCT_coeff[0]) * 192);

    ptr = block_buf;
    DecodeHuffmanDataUnit(YDC_nr, YAC_nr, &DCY, 0);
    InverseDCT(DCT_coeff, ptr, QT_TableSelection);
    ptr += 64;

    DecodeHuffmanDataUnit(CbDC_nr, CbAC_nr, &DCCb, 64);
    InverseDCT(DCT_coeff + 64, ptr, QT_TableSelection + 1);
    ptr += 64;

    DecodeHuffmanDataUnit(CrDC_nr, CrAC_nr, &DCCr, 128);
    InverseDCT(DCT_coeff + 128, ptr, QT_TableSelection + 1);

    YUVToRGBPass2(mbx, mby, block_buf, yuv_buf, out_buf);

    return 0;
}

static void MoveBlockIndex(int *mbx, int *mby)
{
    (*mbx)++;
    if (*mbx >= mbwidth) {
        (*mby)++;
        if (*mby >= mbheight)
            *mby = 0;
        *mbx = 0;
    }
}

static void UpdateXY(int *mbx, int *mby)
{
    *mbx = (cur_data & 0x0FF00000) >> 20;
    *mby = (cur_data & 0x0FF000) >> 12;
}

static void DecodeBuffer(int len, BYTE *out_buf)
{
    int mbx = 0, mby = 0;

    do {
        switch (((cur_data >> 28) & (long)BLOCK_HEADER_MASK)) {
        case JPEG_NO_SKIP_CODE:
            //pr_dbg("(%d, %d): No_skip\n", mbx, mby);
            SkipBits(BLOCK_AST2100_START_LENGTH);
            Decompress(mbx, mby, out_buf, 0);
            MoveBlockIndex(&mbx, &mby);
            break;
        case FRAME_END_CODE:
            //pr_dbg("(%d, %d): end\n", mbx, mby);
            return;
        case JPEG_SKIP_CODE:
            //pr_dbg("(%d, %d): skip\n", mbx, mby);
            UpdateXY(&mbx, &mby);

            SkipBits(BLOCK_AST2100_SKIP_LENGTH);
            Decompress(mbx, mby, out_buf, 0);
            MoveBlockIndex(&mbx, &mby);
            break;
        case JPEG_PASS2_CODE:
            //pr_dbg("(%d, %d): pass2\n", mbx, mby);
            SkipBits(BLOCK_AST2100_START_LENGTH);
            DecompressPASS2(mbx, mby, out_buf, 2);
            MoveBlockIndex(&mbx, &mby);
            break;
        case JPEG_SKIP_PASS2_CODE:
            //pr_dbg("(%d, %d): skip pass2\n", mbx, mby);
            UpdateXY(&mbx, &mby);

            SkipBits(BLOCK_AST2100_SKIP_LENGTH);
            DecompressPASS2(mbx, mby, out_buf, 2);
            MoveBlockIndex(&mbx, &mby);
            break;
        }
    } while (in_buf_index <= len);
}

EMSCRIPTEN_KEEPALIVE
void init(void)
{
    InitBuffer();
    InitTable();
}

EMSCRIPTEN_KEEPALIVE
void decode(unsigned long* _in_buf, int _len, unsigned char* _out_buf, int _width, int _height,
    unsigned _mode420, unsigned _sel, unsigned _adv_sel)
{
    pr_dbg("len(%d) 420(%d) width(%d) height(%d)\n", _len, _mode420, _width, _height);

    if (first_frame == 1 || _sel != selector || _adv_sel != advance_selector) {
        pr_dbg("init table for sel(%d) adv_sel(%d)\n", selector, advance_selector);

        selector = _sel;
        advance_selector = _adv_sel;

        load_quant_table(QT[0]);
        load_quant_tableCb(QT[1]);
        // for 2-pass JPEG
        load_advance_quant_table(QT[2]);
        load_advance_quant_tableCb(QT[3]);
        first_frame = 0;
    }
    width = _width;
    height = _height;
    mode420 = _mode420;

    if (mode420) {
        mbwidth = ALIGN(width, 16) / 16;
        mbheight = ALIGN(height, 16) / 16;
    } else {
        mbwidth = ALIGN(width, 8) / 8;
        mbheight = ALIGN(height, 8) / 8;
    }
    in_buf = _in_buf;

    cur_data = in_buf[0];
    next_data = in_buf[1];
    in_buf_index = 2;

    newbits = 32;
    DCY = DCCb = DCCr = 0;
    DecodeBuffer(_len, _out_buf);
}
