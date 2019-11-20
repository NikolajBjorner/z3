/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    expr_network.cpp

Abstract:

    expr network.

Author:

    Nikolaj Bjorner (nbjorner) 6-14-2019

Revision History:

--*/

#include "ast/expr_network.h"

static uint64_t compute_shift(uint64_t x, unsigned code) {
    switch (code) {
#define _x0 (x & 1)
#define _x1 _x0
    case 1: return _x1;
#define _x2 (_x1 | (_x1 << 1))
    case 2: return _x2;
#define _x3 (_x2 | (_x2 << 2))
    case 4: return _x3;
#define _x4 (_x3 | (_x3 << 4))
    case 8: return _x4;
#define _x5 (_x4 | (_x4 << 8))
    case 16: return _x5;
#define _x6 (_x5 | (_x5 << 16))
    case 32: return _x6;
#define _x7 (_x6 | (_x6 << 32))
    case 64: return _x7;
#define _x8 (x & 3)
#define _x9 _x8
#define _x10 (_x9 | (_x9 << 2))
#define _x11 (_x10 | (_x10 << 4))
#define _x12 (_x11 | (_x11 << 8))
#define _x13 (_x12 | (_x12 << 16))
#define _x14 (_x13 | (_x13 << 32))
    case 65: return _x14;
    case 33: return _x13;
#define _x15 (x & 2)
#define _x16 (_x15 << 1)
#define _x17 (_x16 | (_x16 << 1))
#define _x18 (_x2 | _x17)
#define _x19 (_x18 | (_x18 << 4))
#define _x20 (_x19 | (_x19 << 8))
#define _x21 (_x20 | (_x20 << 16))
#define _x22 (_x21 | (_x21 << 32))
    case 66: return _x22;
#define _x23 (x & 15)
#define _x24 _x23
#define _x25 (_x24 | (_x24 << 4))
#define _x26 (_x25 | (_x25 << 8))
#define _x27 (_x26 | (_x26 << 16))
#define _x28 (_x27 | (_x27 << 32))
    case 67: return _x28;
    case 17: return _x12;
    case 34: return _x21;
#define _x29 (_x15 << 3)
#define _x30 (_x29 | (_x29 << 1))
#define _x31 (_x30 | (_x30 << 2))
#define _x32 (_x3 | _x31)
#define _x33 (_x32 | (_x32 << 8))
#define _x34 (_x33 | (_x33 << 16))
#define _x35 (_x34 | (_x34 << 32))
    case 68: return _x35;
#define _x36 (x & 12)
#define _x37 (_x36 << 2)
#define _x38 (_x37 | (_x37 << 2))
#define _x39 (_x10 | _x38)
#define _x40 (_x39 | (_x39 << 8))
#define _x41 (_x40 | (_x40 << 16))
#define _x42 (_x41 | (_x41 << 32))
    case 69: return _x42;
    case 35: return _x27;
#define _x43 (x & 4)
#define _x44 (_x43 << 2)
#define _x45 (_x44 | (_x44 << 1))
#define _x46 (x & 8)
#define _x47 (_x46 << 3)
#define _x48 (_x47 | (_x47 << 1))
#define _x49 (_x45 | _x48)
#define _x50 (_x18 | _x49)
#define _x51 (_x50 | (_x50 << 8))
#define _x52 (_x51 | (_x51 << 16))
#define _x53 (_x52 | (_x52 << 32))
    case 70: return _x53;
#define _x54 (x & 255)
#define _x55 _x54
#define _x56 (_x55 | (_x55 << 8))
#define _x57 (_x56 | (_x56 << 16))
#define _x58 (_x57 | (_x57 << 32))
    case 71: return _x58;
    case 9: return _x11;
    case 18: return _x20;
    case 36: return _x34;
#define _x59 (_x15 << 7)
#define _x60 (_x59 | (_x59 << 1))
#define _x61 (_x60 | (_x60 << 2))
#define _x62 (_x61 | (_x61 << 4))
#define _x63 (_x4 | _x62)
#define _x64 (_x63 | (_x63 << 16))
#define _x65 (_x64 | (_x64 << 32))
    case 72: return _x65;
#define _x66 (_x36 << 6)
#define _x67 (_x66 | (_x66 << 2))
#define _x68 (_x67 | (_x67 << 4))
#define _x69 (_x11 | _x68)
#define _x70 (_x69 | (_x69 << 16))
#define _x71 (_x70 | (_x70 << 32))
    case 73: return _x71;
    case 37: return _x41;
#define _x72 (_x43 << 6)
#define _x73 (_x72 | (_x72 << 1))
#define _x74 (_x46 << 7)
#define _x75 (_x74 | (_x74 << 1))
#define _x76 (_x73 | _x75)
#define _x77 (_x76 | (_x76 << 4))
#define _x78 (_x19 | _x77)
#define _x79 (_x78 | (_x78 << 16))
#define _x80 (_x79 | (_x79 << 32))
    case 74: return _x80;
#define _x81 (x & 240)
#define _x82 (_x81 << 4)
#define _x83 (_x82 | (_x82 << 4))
#define _x84 (_x25 | _x83)
#define _x85 (_x84 | (_x84 << 16))
#define _x86 (_x85 | (_x85 << 32))
    case 75: return _x86;
    case 19: return _x26;
    case 38: return _x52;
#define _x87 (_x73 | (_x73 << 2))
#define _x88 (_x46 << 9)
#define _x89 (_x88 | (_x88 << 1))
#define _x90 (_x89 | (_x89 << 2))
#define _x91 (_x87 | _x90)
#define _x92 (_x32 | _x91)
#define _x93 (_x92 | (_x92 << 16))
#define _x94 (_x93 | (_x93 << 32))
    case 76: return _x94;
#define _x95 (x & 48)
#define _x96 (_x95 << 4)
#define _x97 (_x96 | (_x96 << 2))
#define _x98 (x & 192)
#define _x99 (_x98 << 6)
#define _x100 (_x99 | (_x99 << 2))
#define _x101 (_x97 | _x100)
#define _x102 (_x39 | _x101)
#define _x103 (_x102 | (_x102 << 16))
#define _x104 (_x103 | (_x103 << 32))
    case 77: return _x104;
    case 39: return _x57;
#define _x105 (x & 16)
#define _x106 (_x105 << 4)
#define _x107 (_x106 | (_x106 << 1))
#define _x108 (x & 32)
#define _x109 (_x108 << 5)
#define _x110 (_x109 | (_x109 << 1))
#define _x111 (_x107 | _x110)
#define _x112 (x & 64)
#define _x113 (_x112 << 6)
#define _x114 (_x113 | (_x113 << 1))
#define _x115 (x & 128)
#define _x116 (_x115 << 7)
#define _x117 (_x116 | (_x116 << 1))
#define _x118 (_x114 | _x117)
#define _x119 (_x111 | _x118)
#define _x120 (_x50 | _x119)
#define _x121 (_x120 | (_x120 << 16))
#define _x122 (_x121 | (_x121 << 32))
    case 78: return _x122;
#define _x123 (x & 65535)
#define _x124 _x123
#define _x125 (_x124 | (_x124 << 16))
#define _x126 (_x125 | (_x125 << 32))
    case 79: return _x126;
    case 5: return _x10;
    case 10: return _x19;
    case 20: return _x33;
    case 40: return _x64;
#define _x127 (_x15 << 15)
#define _x128 (_x127 | (_x127 << 1))
#define _x129 (_x128 | (_x128 << 2))
#define _x130 (_x129 | (_x129 << 4))
#define _x131 (_x130 | (_x130 << 8))
#define _x132 (_x5 | _x131)
#define _x133 (_x132 | (_x132 << 32))
    case 80: return _x133;
#define _x134 (_x36 << 14)
#define _x135 (_x134 | (_x134 << 2))
#define _x136 (_x135 | (_x135 << 4))
#define _x137 (_x136 | (_x136 << 8))
#define _x138 (_x12 | _x137)
#define _x139 (_x138 | (_x138 << 32))
    case 81: return _x139;
    case 41: return _x70;
#define _x140 (_x43 << 14)
#define _x141 (_x140 | (_x140 << 1))
#define _x142 (_x46 << 15)
#define _x143 (_x142 | (_x142 << 1))
#define _x144 (_x141 | _x143)
#define _x145 (_x144 | (_x144 << 4))
#define _x146 (_x145 | (_x145 << 8))
#define _x147 (_x20 | _x146)
#define _x148 (_x147 | (_x147 << 32))
    case 82: return _x148;
#define _x149 (_x81 << 12)
#define _x150 (_x149 | (_x149 << 4))
#define _x151 (_x150 | (_x150 << 8))
#define _x152 (_x26 | _x151)
#define _x153 (_x152 | (_x152 << 32))
    case 83: return _x153;
    case 21: return _x40;
    case 42: return _x79;
#define _x154 (_x141 | (_x141 << 2))
#define _x155 (_x46 << 17)
#define _x156 (_x155 | (_x155 << 1))
#define _x157 (_x156 | (_x156 << 2))
#define _x158 (_x154 | _x157)
#define _x159 (_x158 | (_x158 << 8))
#define _x160 (_x33 | _x159)
#define _x161 (_x160 | (_x160 << 32))
    case 84: return _x161;
#define _x162 (_x95 << 12)
#define _x163 (_x162 | (_x162 << 2))
#define _x164 (_x98 << 14)
#define _x165 (_x164 | (_x164 << 2))
#define _x166 (_x163 | _x165)
#define _x167 (_x166 | (_x166 << 8))
#define _x168 (_x40 | _x167)
#define _x169 (_x168 | (_x168 << 32))
    case 85: return _x169;
    case 43: return _x85;
#define _x170 (_x105 << 12)
#define _x171 (_x170 | (_x170 << 1))
#define _x172 (_x108 << 13)
#define _x173 (_x172 | (_x172 << 1))
#define _x174 (_x171 | _x173)
#define _x175 (_x112 << 14)
#define _x176 (_x175 | (_x175 << 1))
#define _x177 (_x115 << 15)
#define _x178 (_x177 | (_x177 << 1))
#define _x179 (_x176 | _x178)
#define _x180 (_x174 | _x179)
#define _x181 (_x180 | (_x180 << 8))
#define _x182 (_x51 | _x181)
#define _x183 (_x182 | (_x182 << 32))
    case 86: return _x183;
#define _x184 (x & 65280)
#define _x185 (_x184 << 8)
#define _x186 (_x185 | (_x185 << 8))
#define _x187 (_x56 | _x186)
#define _x188 (_x187 | (_x187 << 32))
    case 87: return _x188;
    case 11: return _x25;
    case 22: return _x51;
    case 44: return _x93;
#define _x189 (_x154 | (_x154 << 4))
#define _x190 (_x46 << 21)
#define _x191 (_x190 | (_x190 << 1))
#define _x192 (_x191 | (_x191 << 2))
#define _x193 (_x192 | (_x192 << 4))
#define _x194 (_x189 | _x193)
#define _x195 (_x63 | _x194)
#define _x196 (_x195 | (_x195 << 32))
    case 88: return _x196;
#define _x197 (_x163 | (_x163 << 4))
#define _x198 (_x98 << 18)
#define _x199 (_x198 | (_x198 << 2))
#define _x200 (_x199 | (_x199 << 4))
#define _x201 (_x197 | _x200)
#define _x202 (_x69 | _x201)
#define _x203 (_x202 | (_x202 << 32))
    case 89: return _x203;
    case 45: return _x103;
#define _x204 (_x174 | (_x174 << 4))
#define _x205 (_x112 << 18)
#define _x206 (_x205 | (_x205 << 1))
#define _x207 (_x115 << 19)
#define _x208 (_x207 | (_x207 << 1))
#define _x209 (_x206 | _x208)
#define _x210 (_x209 | (_x209 << 4))
#define _x211 (_x204 | _x210)
#define _x212 (_x78 | _x211)
#define _x213 (_x212 | (_x212 << 32))
    case 90: return _x213;
#define _x214 (x & 3840)
#define _x215 (_x214 << 8)
#define _x216 (_x215 | (_x215 << 4))
#define _x217 (x & 61440)
#define _x218 (_x217 << 12)
#define _x219 (_x218 | (_x218 << 4))
#define _x220 (_x216 | _x219)
#define _x221 (_x84 | _x220)
#define _x222 (_x221 | (_x221 << 32))
    case 91: return _x222;
    case 23: return _x56;
    case 46: return _x121;
#define _x223 (_x171 | (_x171 << 2))
#define _x224 (_x108 << 15)
#define _x225 (_x224 | (_x224 << 1))
#define _x226 (_x225 | (_x225 << 2))
#define _x227 (_x223 | _x226)
#define _x228 (_x206 | (_x206 << 2))
#define _x229 (_x115 << 21)
#define _x230 (_x229 | (_x229 << 1))
#define _x231 (_x230 | (_x230 << 2))
#define _x232 (_x228 | _x231)
#define _x233 (_x227 | _x232)
#define _x234 (_x92 | _x233)
#define _x235 (_x234 | (_x234 << 32))
    case 92: return _x235;
#define _x236 (x & 768)
#define _x237 (_x236 << 8)
#define _x238 (_x237 | (_x237 << 2))
#define _x239 (x & 3072)
#define _x240 (_x239 << 10)
#define _x241 (_x240 | (_x240 << 2))
#define _x242 (_x238 | _x241)
#define _x243 (x & 12288)
#define _x244 (_x243 << 12)
#define _x245 (_x244 | (_x244 << 2))
#define _x246 (x & 49152)
#define _x247 (_x246 << 14)
#define _x248 (_x247 | (_x247 << 2))
#define _x249 (_x245 | _x248)
#define _x250 (_x242 | _x249)
#define _x251 (_x102 | _x250)
#define _x252 (_x251 | (_x251 << 32))
    case 93: return _x252;
    case 47: return _x125;
#define _x253 (x & 256)
#define _x254 (_x253 << 8)
#define _x255 (_x254 | (_x254 << 1))
#define _x256 (x & 512)
#define _x257 (_x256 << 9)
#define _x258 (_x257 | (_x257 << 1))
#define _x259 (_x255 | _x258)
#define _x260 (x & 1024)
#define _x261 (_x260 << 10)
#define _x262 (_x261 | (_x261 << 1))
#define _x263 (x & 2048)
#define _x264 (_x263 << 11)
#define _x265 (_x264 | (_x264 << 1))
#define _x266 (_x262 | _x265)
#define _x267 (_x259 | _x266)
#define _x268 (x & 4096)
#define _x269 (_x268 << 12)
#define _x270 (_x269 | (_x269 << 1))
#define _x271 (x & 8192)
#define _x272 (_x271 << 13)
#define _x273 (_x272 | (_x272 << 1))
#define _x274 (_x270 | _x273)
#define _x275 (x & 16384)
#define _x276 (_x275 << 14)
#define _x277 (_x276 | (_x276 << 1))
#define _x278 (x & 32768)
#define _x279 (_x278 << 15)
#define _x280 (_x279 | (_x279 << 1))
#define _x281 (_x277 | _x280)
#define _x282 (_x274 | _x281)
#define _x283 (_x267 | _x282)
#define _x284 (_x120 | _x283)
#define _x285 (_x284 | (_x284 << 32))
    case 94: return _x285;
#define _x286 (x & 4294967295)
#define _x287 _x286
#define _x288 (_x287 | (_x287 << 32))
    case 95: return _x288;
    case 3: return _x9;
    case 6: return _x18;
    case 12: return _x32;
    case 24: return _x63;
    case 48: return _x132;
#define _x289 (_x15 << 31)
#define _x290 (_x289 | (_x289 << 1))
#define _x291 (_x290 | (_x290 << 2))
#define _x292 (_x291 | (_x291 << 4))
#define _x293 (_x292 | (_x292 << 8))
#define _x294 (_x293 | (_x293 << 16))
#define _x295 (_x6 | _x294)
    case 96: return _x295;
#define _x296 (_x36 << 30)
#define _x297 (_x296 | (_x296 << 2))
#define _x298 (_x297 | (_x297 << 4))
#define _x299 (_x298 | (_x298 << 8))
#define _x300 (_x299 | (_x299 << 16))
#define _x301 (_x13 | _x300)
    case 97: return _x301;
    case 49: return _x138;
#define _x302 (_x43 << 30)
#define _x303 (_x302 | (_x302 << 1))
#define _x304 (_x46 << 31)
#define _x305 (_x304 | (_x304 << 1))
#define _x306 (_x303 | _x305)
#define _x307 (_x306 | (_x306 << 4))
#define _x308 (_x307 | (_x307 << 8))
#define _x309 (_x308 | (_x308 << 16))
#define _x310 (_x21 | _x309)
    case 98: return _x310;
#define _x311 (_x81 << 28)
#define _x312 (_x311 | (_x311 << 4))
#define _x313 (_x312 | (_x312 << 8))
#define _x314 (_x313 | (_x313 << 16))
#define _x315 (_x27 | _x314)
    case 99: return _x315;
    case 25: return _x69;
    case 50: return _x147;
#define _x316 (_x303 | (_x303 << 2))
#define _x317 (_x46 << 33)
#define _x318 (_x317 | (_x317 << 1))
#define _x319 (_x318 | (_x318 << 2))
#define _x320 (_x316 | _x319)
#define _x321 (_x320 | (_x320 << 8))
#define _x322 (_x321 | (_x321 << 16))
#define _x323 (_x34 | _x322)
    case 100: return _x323;
#define _x324 (_x95 << 28)
#define _x325 (_x324 | (_x324 << 2))
#define _x326 (_x98 << 30)
#define _x327 (_x326 | (_x326 << 2))
#define _x328 (_x325 | _x327)
#define _x329 (_x328 | (_x328 << 8))
#define _x330 (_x329 | (_x329 << 16))
#define _x331 (_x41 | _x330)
    case 101: return _x331;
    case 51: return _x152;
#define _x332 (_x105 << 28)
#define _x333 (_x332 | (_x332 << 1))
#define _x334 (_x108 << 29)
#define _x335 (_x334 | (_x334 << 1))
#define _x336 (_x333 | _x335)
#define _x337 (_x112 << 30)
#define _x338 (_x337 | (_x337 << 1))
#define _x339 (_x115 << 31)
#define _x340 (_x339 | (_x339 << 1))
#define _x341 (_x338 | _x340)
#define _x342 (_x336 | _x341)
#define _x343 (_x342 | (_x342 << 8))
#define _x344 (_x343 | (_x343 << 16))
#define _x345 (_x52 | _x344)
    case 102: return _x345;
#define _x346 (_x184 << 24)
#define _x347 (_x346 | (_x346 << 8))
#define _x348 (_x347 | (_x347 << 16))
#define _x349 (_x57 | _x348)
    case 103: return _x349;
    case 13: return _x39;
    case 26: return _x78;
    case 52: return _x160;
#define _x350 (_x316 | (_x316 << 4))
#define _x351 (_x46 << 37)
#define _x352 (_x351 | (_x351 << 1))
#define _x353 (_x352 | (_x352 << 2))
#define _x354 (_x353 | (_x353 << 4))
#define _x355 (_x350 | _x354)
#define _x356 (_x355 | (_x355 << 16))
#define _x357 (_x64 | _x356)
    case 104: return _x357;
#define _x358 (_x325 | (_x325 << 4))
#define _x359 (_x98 << 34)
#define _x360 (_x359 | (_x359 << 2))
#define _x361 (_x360 | (_x360 << 4))
#define _x362 (_x358 | _x361)
#define _x363 (_x362 | (_x362 << 16))
#define _x364 (_x70 | _x363)
    case 105: return _x364;
    case 53: return _x168;
#define _x365 (_x336 | (_x336 << 4))
#define _x366 (_x112 << 34)
#define _x367 (_x366 | (_x366 << 1))
#define _x368 (_x115 << 35)
#define _x369 (_x368 | (_x368 << 1))
#define _x370 (_x367 | _x369)
#define _x371 (_x370 | (_x370 << 4))
#define _x372 (_x365 | _x371)
#define _x373 (_x372 | (_x372 << 16))
#define _x374 (_x79 | _x373)
    case 106: return _x374;
#define _x375 (_x214 << 24)
#define _x376 (_x375 | (_x375 << 4))
#define _x377 (_x217 << 28)
#define _x378 (_x377 | (_x377 << 4))
#define _x379 (_x376 | _x378)
#define _x380 (_x379 | (_x379 << 16))
#define _x381 (_x85 | _x380)
    case 107: return _x381;
    case 27: return _x84;
    case 54: return _x182;
#define _x382 (_x333 | (_x333 << 2))
#define _x383 (_x108 << 31)
#define _x384 (_x383 | (_x383 << 1))
#define _x385 (_x384 | (_x384 << 2))
#define _x386 (_x382 | _x385)
#define _x387 (_x367 | (_x367 << 2))
#define _x388 (_x115 << 37)
#define _x389 (_x388 | (_x388 << 1))
#define _x390 (_x389 | (_x389 << 2))
#define _x391 (_x387 | _x390)
#define _x392 (_x386 | _x391)
#define _x393 (_x392 | (_x392 << 16))
#define _x394 (_x93 | _x393)
    case 108: return _x394;
#define _x395 (_x236 << 24)
#define _x396 (_x395 | (_x395 << 2))
#define _x397 (_x239 << 26)
#define _x398 (_x397 | (_x397 << 2))
#define _x399 (_x396 | _x398)
#define _x400 (_x243 << 28)
#define _x401 (_x400 | (_x400 << 2))
#define _x402 (_x246 << 30)
#define _x403 (_x402 | (_x402 << 2))
#define _x404 (_x401 | _x403)
#define _x405 (_x399 | _x404)
#define _x406 (_x405 | (_x405 << 16))
#define _x407 (_x103 | _x406)
    case 109: return _x407;
    case 55: return _x187;
#define _x408 (_x253 << 24)
#define _x409 (_x408 | (_x408 << 1))
#define _x410 (_x256 << 25)
#define _x411 (_x410 | (_x410 << 1))
#define _x412 (_x409 | _x411)
#define _x413 (_x260 << 26)
#define _x414 (_x413 | (_x413 << 1))
#define _x415 (_x263 << 27)
#define _x416 (_x415 | (_x415 << 1))
#define _x417 (_x414 | _x416)
#define _x418 (_x412 | _x417)
#define _x419 (_x268 << 28)
#define _x420 (_x419 | (_x419 << 1))
#define _x421 (_x271 << 29)
#define _x422 (_x421 | (_x421 << 1))
#define _x423 (_x420 | _x422)
#define _x424 (_x275 << 30)
#define _x425 (_x424 | (_x424 << 1))
#define _x426 (_x278 << 31)
#define _x427 (_x426 | (_x426 << 1))
#define _x428 (_x425 | _x427)
#define _x429 (_x423 | _x428)
#define _x430 (_x418 | _x429)
#define _x431 (_x430 | (_x430 << 16))
#define _x432 (_x121 | _x431)
    case 110: return _x432;
#define _x433 (x & 4294901760)
#define _x434 (_x433 << 16)
#define _x435 (_x434 | (_x434 << 16))
#define _x436 (_x125 | _x435)
    case 111: return _x436;
    case 7: return _x24;
    case 14: return _x50;
    case 28: return _x92;
    case 56: return _x195;
#define _x437 (_x350 | (_x350 << 8))
#define _x438 (_x46 << 45)
#define _x439 (_x438 | (_x438 << 1))
#define _x440 (_x439 | (_x439 << 2))
#define _x441 (_x440 | (_x440 << 4))
#define _x442 (_x441 | (_x441 << 8))
#define _x443 (_x437 | _x442)
#define _x444 (_x132 | _x443)
    case 112: return _x444;
#define _x445 (_x358 | (_x358 << 8))
#define _x446 (_x98 << 42)
#define _x447 (_x446 | (_x446 << 2))
#define _x448 (_x447 | (_x447 << 4))
#define _x449 (_x448 | (_x448 << 8))
#define _x450 (_x445 | _x449)
#define _x451 (_x138 | _x450)
    case 113: return _x451;
    case 57: return _x202;
#define _x452 (_x365 | (_x365 << 8))
#define _x453 (_x112 << 42)
#define _x454 (_x453 | (_x453 << 1))
#define _x455 (_x115 << 43)
#define _x456 (_x455 | (_x455 << 1))
#define _x457 (_x454 | _x456)
#define _x458 (_x457 | (_x457 << 4))
#define _x459 (_x458 | (_x458 << 8))
#define _x460 (_x452 | _x459)
#define _x461 (_x147 | _x460)
    case 114: return _x461;
#define _x462 (_x376 | (_x376 << 8))
#define _x463 (_x217 << 36)
#define _x464 (_x463 | (_x463 << 4))
#define _x465 (_x464 | (_x464 << 8))
#define _x466 (_x462 | _x465)
#define _x467 (_x152 | _x466)
    case 115: return _x467;
    case 29: return _x102;
    case 58: return _x212;
#define _x468 (_x386 | (_x386 << 8))
#define _x469 (_x454 | (_x454 << 2))
#define _x470 (_x115 << 45)
#define _x471 (_x470 | (_x470 << 1))
#define _x472 (_x471 | (_x471 << 2))
#define _x473 (_x469 | _x472)
#define _x474 (_x473 | (_x473 << 8))
#define _x475 (_x468 | _x474)
#define _x476 (_x160 | _x475)
    case 116: return _x476;
#define _x477 (_x399 | (_x399 << 8))
#define _x478 (_x243 << 36)
#define _x479 (_x478 | (_x478 << 2))
#define _x480 (_x246 << 38)
#define _x481 (_x480 | (_x480 << 2))
#define _x482 (_x479 | _x481)
#define _x483 (_x482 | (_x482 << 8))
#define _x484 (_x477 | _x483)
#define _x485 (_x168 | _x484)
    case 117: return _x485;
    case 59: return _x221;
#define _x486 (_x418 | (_x418 << 8))
#define _x487 (_x268 << 36)
#define _x488 (_x487 | (_x487 << 1))
#define _x489 (_x271 << 37)
#define _x490 (_x489 | (_x489 << 1))
#define _x491 (_x488 | _x490)
#define _x492 (_x275 << 38)
#define _x493 (_x492 | (_x492 << 1))
#define _x494 (_x278 << 39)
#define _x495 (_x494 | (_x494 << 1))
#define _x496 (_x493 | _x495)
#define _x497 (_x491 | _x496)
#define _x498 (_x497 | (_x497 << 8))
#define _x499 (_x486 | _x498)
#define _x500 (_x182 | _x499)
    case 118: return _x500;
#define _x501 (x & 16711680)
#define _x502 (_x501 << 16)
#define _x503 (_x502 | (_x502 << 8))
#define _x504 (x & 4278190080)
#define _x505 (_x504 << 24)
#define _x506 (_x505 | (_x505 << 8))
#define _x507 (_x503 | _x506)
#define _x508 (_x187 | _x507)
    case 119: return _x508;
    case 15: return _x55;
    case 30: return _x120;
    case 60: return _x234;
#define _x509 (_x382 | (_x382 << 4))
#define _x510 (_x108 << 35)
#define _x511 (_x510 | (_x510 << 1))
#define _x512 (_x511 | (_x511 << 2))
#define _x513 (_x512 | (_x512 << 4))
#define _x514 (_x509 | _x513)
#define _x515 (_x469 | (_x469 << 4))
#define _x516 (_x115 << 49)
#define _x517 (_x516 | (_x516 << 1))
#define _x518 (_x517 | (_x517 << 2))
#define _x519 (_x518 | (_x518 << 4))
#define _x520 (_x515 | _x519)
#define _x521 (_x514 | _x520)
#define _x522 (_x195 | _x521)
    case 120: return _x522;
#define _x523 (_x396 | (_x396 << 4))
#define _x524 (_x239 << 30)
#define _x525 (_x524 | (_x524 << 2))
#define _x526 (_x525 | (_x525 << 4))
#define _x527 (_x523 | _x526)
#define _x528 (_x479 | (_x479 << 4))
#define _x529 (_x246 << 42)
#define _x530 (_x529 | (_x529 << 2))
#define _x531 (_x530 | (_x530 << 4))
#define _x532 (_x528 | _x531)
#define _x533 (_x527 | _x532)
#define _x534 (_x202 | _x533)
    case 121: return _x534;
    case 61: return _x251;
#define _x535 (_x412 | (_x412 << 4))
#define _x536 (_x260 << 30)
#define _x537 (_x536 | (_x536 << 1))
#define _x538 (_x263 << 31)
#define _x539 (_x538 | (_x538 << 1))
#define _x540 (_x537 | _x539)
#define _x541 (_x540 | (_x540 << 4))
#define _x542 (_x535 | _x541)
#define _x543 (_x491 | (_x491 << 4))
#define _x544 (_x275 << 42)
#define _x545 (_x544 | (_x544 << 1))
#define _x546 (_x278 << 43)
#define _x547 (_x546 | (_x546 << 1))
#define _x548 (_x545 | _x547)
#define _x549 (_x548 | (_x548 << 4))
#define _x550 (_x543 | _x549)
#define _x551 (_x542 | _x550)
#define _x552 (_x212 | _x551)
    case 122: return _x552;
#define _x553 (x & 983040)
#define _x554 (_x553 << 16)
#define _x555 (_x554 | (_x554 << 4))
#define _x556 (x & 15728640)
#define _x557 (_x556 << 20)
#define _x558 (_x557 | (_x557 << 4))
#define _x559 (_x555 | _x558)
#define _x560 (x & 251658240)
#define _x561 (_x560 << 24)
#define _x562 (_x561 | (_x561 << 4))
#define _x563 (x & 4026531840)
#define _x564 (_x563 << 28)
#define _x565 (_x564 | (_x564 << 4))
#define _x566 (_x562 | _x565)
#define _x567 (_x559 | _x566)
#define _x568 (_x221 | _x567)
    case 123: return _x568;
    case 31: return _x124;
    case 62: return _x284;
#define _x569 (_x409 | (_x409 << 2))
#define _x570 (_x256 << 27)
#define _x571 (_x570 | (_x570 << 1))
#define _x572 (_x571 | (_x571 << 2))
#define _x573 (_x569 | _x572)
#define _x574 (_x537 | (_x537 << 2))
#define _x575 (_x263 << 33)
#define _x576 (_x575 | (_x575 << 1))
#define _x577 (_x576 | (_x576 << 2))
#define _x578 (_x574 | _x577)
#define _x579 (_x573 | _x578)
#define _x580 (_x488 | (_x488 << 2))
#define _x581 (_x271 << 39)
#define _x582 (_x581 | (_x581 << 1))
#define _x583 (_x582 | (_x582 << 2))
#define _x584 (_x580 | _x583)
#define _x585 (_x545 | (_x545 << 2))
#define _x586 (_x278 << 45)
#define _x587 (_x586 | (_x586 << 1))
#define _x588 (_x587 | (_x587 << 2))
#define _x589 (_x585 | _x588)
#define _x590 (_x584 | _x589)
#define _x591 (_x579 | _x590)
#define _x592 (_x234 | _x591)
    case 124: return _x592;
#define _x593 (x & 196608)
#define _x594 (_x593 << 16)
#define _x595 (_x594 | (_x594 << 2))
#define _x596 (x & 786432)
#define _x597 (_x596 << 18)
#define _x598 (_x597 | (_x597 << 2))
#define _x599 (_x595 | _x598)
#define _x600 (x & 3145728)
#define _x601 (_x600 << 20)
#define _x602 (_x601 | (_x601 << 2))
#define _x603 (x & 12582912)
#define _x604 (_x603 << 22)
#define _x605 (_x604 | (_x604 << 2))
#define _x606 (_x602 | _x605)
#define _x607 (_x599 | _x606)
#define _x608 (x & 50331648)
#define _x609 (_x608 << 24)
#define _x610 (_x609 | (_x609 << 2))
#define _x611 (x & 201326592)
#define _x612 (_x611 << 26)
#define _x613 (_x612 | (_x612 << 2))
#define _x614 (_x610 | _x613)
#define _x615 (x & 805306368)
#define _x616 (_x615 << 28)
#define _x617 (_x616 | (_x616 << 2))
#define _x618 (x & 3221225472)
#define _x619 (_x618 << 30)
#define _x620 (_x619 | (_x619 << 2))
#define _x621 (_x617 | _x620)
#define _x622 (_x614 | _x621)
#define _x623 (_x607 | _x622)
#define _x624 (_x251 | _x623)
    case 125: return _x624;
    case 63: return _x287;
#define _x625 (x & 65536)
#define _x626 (_x625 << 16)
#define _x627 (_x626 | (_x626 << 1))
#define _x628 (x & 131072)
#define _x629 (_x628 << 17)
#define _x630 (_x629 | (_x629 << 1))
#define _x631 (_x627 | _x630)
#define _x632 (x & 262144)
#define _x633 (_x632 << 18)
#define _x634 (_x633 | (_x633 << 1))
#define _x635 (x & 524288)
#define _x636 (_x635 << 19)
#define _x637 (_x636 | (_x636 << 1))
#define _x638 (_x634 | _x637)
#define _x639 (_x631 | _x638)
#define _x640 (x & 1048576)
#define _x641 (_x640 << 20)
#define _x642 (_x641 | (_x641 << 1))
#define _x643 (x & 2097152)
#define _x644 (_x643 << 21)
#define _x645 (_x644 | (_x644 << 1))
#define _x646 (_x642 | _x645)
#define _x647 (x & 4194304)
#define _x648 (_x647 << 22)
#define _x649 (_x648 | (_x648 << 1))
#define _x650 (x & 8388608)
#define _x651 (_x650 << 23)
#define _x652 (_x651 | (_x651 << 1))
#define _x653 (_x649 | _x652)
#define _x654 (_x646 | _x653)
#define _x655 (_x639 | _x654)
#define _x656 (x & 16777216)
#define _x657 (_x656 << 24)
#define _x658 (_x657 | (_x657 << 1))
#define _x659 (x & 33554432)
#define _x660 (_x659 << 25)
#define _x661 (_x660 | (_x660 << 1))
#define _x662 (_x658 | _x661)
#define _x663 (x & 67108864)
#define _x664 (_x663 << 26)
#define _x665 (_x664 | (_x664 << 1))
#define _x666 (x & 134217728)
#define _x667 (_x666 << 27)
#define _x668 (_x667 | (_x667 << 1))
#define _x669 (_x665 | _x668)
#define _x670 (_x662 | _x669)
#define _x671 (x & 268435456)
#define _x672 (_x671 << 28)
#define _x673 (_x672 | (_x672 << 1))
#define _x674 (x & 536870912)
#define _x675 (_x674 << 29)
#define _x676 (_x675 | (_x675 << 1))
#define _x677 (_x673 | _x676)
#define _x678 (x & 1073741824)
#define _x679 (_x678 << 30)
#define _x680 (_x679 | (_x679 << 1))
#define _x681 (x & 2147483648)
#define _x682 (_x681 << 31)
#define _x683 (_x682 | (_x682 << 1))
#define _x684 (_x680 | _x683)
#define _x685 (_x677 | _x684)
#define _x686 (_x670 | _x685)
#define _x687 (_x655 | _x686)
#define _x688 (_x284 | _x687)
    case 126: return _x688;
    case 127: return x;
    default:
        UNREACHABLE();
        return 0;
    }
}

void expr_network::add_root(expr* e) {
    m_roots.push_back(e);
    svector<std::pair<expr*,expr*>> todo;
    todo.push_back(std::make_pair(e, nullptr));
    for (unsigned i = 0; i < todo.size(); ++i) {
        expr* e = todo[i].first;
        expr* p = todo[i].second;
        unsigned id = e->get_id();
        while (id >= m_nodes.size()) {
            expr_ref tmp(m);
            m_nodes.push_back(node(tmp));
        }
        node& n = m_nodes[id];
        if (p) {
            n.m_parents.push_back(p->get_id());
        }
        if (!n.m_expr && is_app(e)) {
            for (expr* arg : *to_app(e)) {
                n.m_children.push_back(arg->get_id());
                todo.push_back(std::make_pair(arg, e));
            }
        }
        n.m_expr = e;
    }
}

expr_ref_vector expr_network::get_roots() {
    unsigned_vector todo;
    todo.reserve(m_nodes.size(), 0);
    todo.reset();

    for (expr* r : m_roots) {
        todo.push_back(r->get_id());
    }
    expr_ref_vector node2expr(m);
    svector<bool> valid;
    ptr_vector<expr> args;
    valid.reserve(m_nodes.size(), false);
    for (auto const& n : m_nodes) {
        node2expr.push_back(n.m_expr);
    }
    while (!todo.empty()) {
        unsigned id = todo.back();
        if (valid[id]) {            
            todo.pop_back();
            continue;
        }
        bool all_valid = true;
        args.reset();
        for (unsigned child : m_nodes[id].m_children) {
            if (!valid[child]) {
                todo.push_back(child);
                all_valid = false;
            }
            else if (all_valid) {
                args.push_back(node2expr.get(child));
            }
        }
        if (all_valid) {
            expr* e = m_nodes[id].e();
            if (is_app(e)) {
                bool diff = false;
                for (unsigned i = args.size(); i-- > 0 && !diff; ) {
                    diff = args.get(i) != to_app(e)->get_arg(i);
                }
                func_decl* f = to_app(e)->get_decl();
                if (!diff) {
                    node2expr[id] = e;
                }
                else if (m.is_or(f)) {
                    node2expr[id] = m.mk_or(args.size(), args.c_ptr());
                }
                else if (m.is_and(f)) {
                    node2expr[id] = m.mk_and(args.size(), args.c_ptr());
                }
                else {
                    node2expr[id] = m.mk_app(f, args.size(), args.c_ptr());
                }
            }
            else {
                node2expr[id] = e;
            }
            valid[id] = true;
            todo.pop_back();
        }
    }
    expr_ref_vector result(m);
    for (expr* r : m_roots) {
        result.push_back(node2expr.get(r->get_id()));
    }
    return result;
}

void expr_network::substitute(unsigned src, unsigned dst) {
    if (src == dst) {
        return;
    }
    for (unsigned parent : m_nodes[src].m_parents) {
        for (unsigned& ch : m_nodes[parent].m_children) {
            if (ch == src) {
                ch = dst;
            }
        }
    }
    m_nodes[src].m_parents.reset();
}

unsigned_vector expr_network::top_sort() {
    unsigned_vector result;
    svector<bool> visit;
    visit.reserve(m_nodes.size(), false);
    unsigned_vector todo;
    for (node const& n : m_nodes) {
        if (n.e()) todo.push_back(n.id());
    }
    while (!todo.empty()) {
        unsigned id = todo.back();
        if (visit[id]) {
            todo.pop_back();
            continue;
        }
        bool all_visit = true;
        for (unsigned child : m_nodes[id].m_children) {
            if (!visit[child]) {
                todo.push_back(child);
                all_visit = false;
            }
        }
        if (all_visit) {
            visit[id] = true;
            result.push_back(id);
            todo.pop_back();
        }
    }
    return result;
}

vector<expr_network::cut_set> expr_network::get_cuts(unsigned max_cut_size, unsigned max_cutset_size) {
    unsigned_vector sorted = top_sort();
    vector<cut_set> cuts;
    cuts.resize(m_nodes.size());
    cut_set cut_set2;
    for (unsigned id : sorted) {
        auto& cut_set = cuts[id];
        SASSERT(cut_set.empty());
        node const& n = m_nodes[id];
        if (is_ite(n)) {
            for (auto const& a : cuts[n.m_children[0]]) {
                for (auto const& b : cuts[n.m_children[1]]) {
                    cut ab;
                    if (!ab.merge(a, b)) {
                        continue;
                    }
                    for (auto const& c : cuts[n.m_children[2]]) {
                        cut abc;
                        if (!abc.merge(ab, c)) {
                            continue;
                        }
                        uint64_t t1 = a.shift_table(abc);
                        uint64_t t2 = b.shift_table(abc);
                        uint64_t t3 = c.shift_table(abc);
                        abc.m_table = (t1 & t2) | (~t1 & t3);
                        cut_set.insert(abc);
                        if (cut_set.size() >= max_cutset_size) break;
                    } 
                }
            }
        }
        else if (is_not(n)) {
            for (auto const& a : cuts[n.m_children[0]]) {
                cut_set.push_back(a);
                cut_set.back().m_table = ~a.m_table;
            }
        }
        else if ((is_ac_bool_op(n)) && n.m_children.size() < max_cut_size) {
            bool first = true;
            for (unsigned child : n.m_children) {
                if (first) {
                    for (auto const& a : cuts[child]) {
                        cut_set.push_back(a);
                    }
                    first = false;
                    continue;
                }
                cut_set2.reset();
                for (auto const& a : cut_set) {
                    for (auto const& b : cuts[child]) {
                        cut c;
                        if (c.merge(a, b)) {
                            uint64_t t1 = a.shift_table(c);
                            uint64_t t2 = b.shift_table(c);
                            switch (get_decl_kind(n)) {
                            case OP_AND: c.m_table = t1 & t2; break;
                            case OP_OR:  c.m_table = t1 | t2; break;
                            case OP_XOR: c.m_table = t1 ^ t2; break;
                            case OP_EQ:  c.m_table = ~(t1 ^ t2); break;
                            default: UNREACHABLE(); break;
                            }
                            cut_set2.insert(c);
                        }
                    }
                    if (cut_set2.size() >= max_cutset_size) break;
                }
                cut_set.swap(cut_set2);
            }
        }
        cut_set.push_back(cut(id));
    }
    return cuts;
}

unsigned expr_network::depth(unsigned id) const {
    return get_depth(m_nodes[id].e());
}


bool expr_network::is_not(node const& n) const {
    return n.e() && m.is_not(n.e());
}

bool expr_network::is_ac_bool_op(node const& n) const {
    return n.e() && (m.is_and(n.e()) || m.is_or(n.e()) || m.is_iff(n.e()) || m.is_xor(n.e()));
}

bool expr_network::is_ite(node const& n) const {
    return n.e() && m.is_ite(n.e()) && m.is_bool(to_app(n.e())->get_arg(1));
}

decl_kind expr_network::get_decl_kind(node const& n) const {
    return to_app(n.e())->get_decl_kind();
}

/**
   \brief
   if c is subsumed by a member in cut_set, then c is not inserted.
   otherwise, remove members that c subsumes.
   Note that the cut_set maintains invariant that elements don't subsume each-other.

   TBD: this is a bottleneck.
   Ideas:
   - add Bloom filter to is_subset_of operation.
   - pre-allocate fixed array instead of vector for cut_set to avoid overhead for memory allocation.
 */

void expr_network::cut_set::insert(cut const& c) {
    unsigned i = 0, j = 0;
    for (; i < size(); ++i) {
        cut const& a = (*this)[i];
        if (a.subset_of(c)) {
            return;
        }
        if (c.subset_of(a)) {
            continue;
        }
        else if (j < i) {
            (*this)[j] = a;
        }
        SASSERT(!(a == c));
        ++j;
    }
    shrink(j);    
    push_back(c);
}

bool expr_network::cut_set::no_duplicates() const {
    hashtable<cut const*, cut::hash_proc, cut::eq_proc> table;
    for (auto const& cut : *this) {
        VERIFY(!table.contains(&cut));
        table.insert(&cut);
    }
    return true;
}


/**
   \brief shift table 'a' by adding elements from 'c'.
   a.shift_table(c)

   \pre 'a' is a subset of 'c'.

   Let 't' be the table for 'a'.

   i'th bit in t  is function of indices x0*2^0 + x2*2^1 = i
   i'th bit in t' is function of indices x0*2^0 + x1*2^1 + x2*2^2 = i

   i -> assignment to coefficients in c, 
     -> assignment to coefficients in a
     -> compute j, 
     -> t'[i] <- t'[j]

     This is still time consuming:
     Ideas: 
     - pre-compute some shift operations.
     - use strides on some common cases.
     - what ABC does?
 */


uint64_t expr_network::cut::shift_table(cut const& c) const {
    SASSERT(subset_of(c));
    uint64_t r = 0;
#if 0
    unsigned coeff[max_size+1];
#endif
    unsigned index = 0;
    for (unsigned i = 0, j = 0, x = (*this)[i], y = c[j]; x != UINT_MAX; ) {
        if (x == y) {
#if 0
            coeff[i] = (1 << j);
#endif
            index |= (1 << j);
            x = (*this)[++i];
        }
        y = c[++j];
    }
    index |= (1 << c.m_size);

#if 0
    unsigned new_sz = c.m_size;
    for (unsigned j = 0; j < (1u << new_sz); ++j) {
        unsigned k = 0;
        for (unsigned i = 0; i < m_size; ++i) {
            if (0 != (j & coeff[i])) {
                k += (1 << i);
            }
        }
        r |= ((m_table & (1ull << k)) << (j - k));
    }
#else 
    r = compute_shift(m_table, index);
#endif
    return r;
}

bool expr_network::cut::operator==(cut const& other) const {
    if (m_size != other.m_size) return false;
    if (m_table != other.m_table) return false;
    for (unsigned i = 0; i < m_size; ++i) {
        if ((*this)[i] != other[i]) return false;
    }
    return true;
}

unsigned expr_network::cut::hash() const {
    return get_composite_hash(*this, m_size, 
                              [](cut const& c) { return (unsigned)c.m_table; }, 
                              [](cut const& c, unsigned i) { return c[i]; });
}

std::ostream& expr_network::cut::display(std::ostream& out) const {
    for (unsigned i = 0; i < m_size; ++i) {
        out << (*this)[i] << " ";
    }
    out << "t: ";
    for (unsigned i = 0; i < (1u << m_size); ++i) {
        if (0 != (m_table & (1ull << i))) out << "1"; else out << "0";
    }    
    return out;
}

void expr_network::cut::sort() {
    std::sort(m_elems, m_elems + m_size);
}


#if 0

def consecutive(S):
    for k in range(len(S)-1):
        if S[k] + 1 != S[k+1]:
            return False
    return True

def shift(x, k):
    if k == 0:
        return x
    if k < 0:
        return "(%s >> %d)" % (x,-k)
    return "(%s << %d)" % (x, k)

def hash(r, hashcons):
    if r in hashcons:
        return hashcons[r]
    id = "_x%d" % len(hashcons)
    print ("#define %s %s" % (id, r))
    hashcons[r] = id
    return id

def compile(S, offset, hashcons):
    if consecutive(S):
        k = S[0]
        l = len(S)
        if l == 64:
            return "x"
        mask = ((1 << l)-1) << k
        return hash(shift(hash("(x & %d)" % mask, hashcons), offset - k), hashcons)
    l2 = len(S) >> 1
    S1 = S[0:l2]
    S2 = S[l2:]
    if S1 == S2:
        r1 = compile(S1, offset, hashcons)        
        return hash("(%s | (%s << %d))" % (r1, r1, l2), hashcons)
    r1 = compile(S1, offset, hashcons)
    r2 = compile(S2, offset + l2, hashcons)
    return hash("(%s | %s)" % (r1, r2), hashcons)

def mems2index(mems, bound):
    k = 0
    i = 0
    for m in mems:
        if m:
            k |= (1 << i)
        i += 1
    k |= (1 << i)
    return k

def precompute(mems, bound, hashcons):
    K = 0
    j = 0
    coeff = {}
    deficit = {}
    for m in mems:
        if m:
            coeff[K] = (1 << j)
            deficit[K] = j - K
            K += 1
        j += 1
    indices = []
    for j in range(1 << len(mems)):
        k = 0
        for i in range(K):
            if 0 != (j & coeff[i]):
                k += (1 << i)
        indices += [k]
    idx = mems2index(mems, bound)
    instr = compile(indices, 0, hashcons)
    print("    case %d: return %s;" % (idx, instr))

def combinations(mems, n, m, hashcons):
    if n == 0:
        return
    precompute(mems, m, hashcons)
    combinations([False] + mems, n - 1, m, hashcons)
    combinations([True] + mems, n - 1, m, hashcons)

hashcons = {}
combinations([], 7, 7, hashcons)
        
#endif
