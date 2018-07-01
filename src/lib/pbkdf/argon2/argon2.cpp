/**
* (C) 2018 Jack Lloyd
*
* Botan is released under the Simplified BSD License (see license.txt)
*/

#include <botan/argon2.h>
#include <botan/blake2b.h>
#include <botan/exceptn.h>

#include <iostream>
#include <botan/hex.h>

namespace Botan {

namespace {

static const size_t SYNC_POINTS = 4;

secure_vector<uint8_t> argon2_H0(HashFunction& blake2b,
                                 size_t output_len,
                                 const std::string& password,
                                 const uint8_t salt[], size_t salt_len,
                                 const uint8_t key[], size_t key_len,
                                 const uint8_t ad[], size_t ad_len,
                                 size_t y, size_t p, size_t M, size_t t)
   {
   const uint8_t v = 19; // Argon2 version code

   blake2b.update_le<uint32_t>(p);
   blake2b.update_le<uint32_t>(output_len);
   blake2b.update_le<uint32_t>(M);
   blake2b.update_le<uint32_t>(t);
   blake2b.update_le<uint32_t>(v);
   blake2b.update_le<uint32_t>(y);

   blake2b.update_le<uint32_t>(password.size());
   blake2b.update(password);

   blake2b.update_le<uint32_t>(salt_len);
   blake2b.update(salt, salt_len);

   blake2b.update_le<uint32_t>(key_len);
   blake2b.update(key, key_len);

   blake2b.update_le<uint32_t>(ad_len);
   blake2b.update(ad, ad_len);

   return blake2b.final();
   }

void Htick(uint8_t output[],
           size_t output_len,
           HashFunction& blake2b,
           const secure_vector<uint8_t>& H0,
           size_t p0, size_t p1)
   {
   if(output_len <= 64)
      {
      // TODO:
      //return Htick_short(output, output_len, H0, p0, p1);
      throw Invalid_State("Htick output length too short");
      }

   secure_vector<uint8_t> B(blake2b.output_length());

   blake2b.update_le<uint32_t>(output_len);
   blake2b.update(H0);
   blake2b.update_le<uint32_t>(p0);
   blake2b.update_le<uint32_t>(p1);

   blake2b.final(&B[0]);

   while(output_len > 64)
      {
      copy_mem(output, &B[0], 32);
      output_len -= 32;
      output += 32;

      blake2b.update(B);
      blake2b.final(&B[0]);
      }

   if(output_len > 0)
      copy_mem(output, &B[0], output_len);
   }

void init_blocks(secure_vector<uint64_t>& B,
                 HashFunction& blake2b,
                 const secure_vector<uint8_t>& H0,
                 size_t memory,
                 size_t threads)
   {
   BOTAN_ASSERT_NOMSG(B.size() >= threads*256);

   secure_vector<uint8_t> H(1024);

   for(size_t i = 0; i != threads; ++i)
      {
      const size_t B_off = i * (memory / threads);

      BOTAN_ASSERT_NOMSG(B.size() >= 128*(B_off+2));

      Htick(&H[0], H.size(), blake2b, H0, 0, i);

      for(size_t j = 0; j != 128; ++j)
         {
         B[128*B_off+j] = load_le<uint64_t>(H.data(), j);
         }

      Htick(&H[0], H.size(), blake2b, H0, 1, i);

      for(size_t j = 0; j != 128; ++j)
         {
         B[128*(B_off+1)+j] = load_le<uint64_t>(H.data(), j);
         }
      }

   for(size_t i = 0; i != B.size(); ++i)
      printf("B[%d][%d] = %016llX\n", i/128, i%128, B[i]);
   }

inline void blamka_G(uint64_t& A, uint64_t& B, uint64_t& C, uint64_t& D)
   {
   A += B + 2*static_cast<uint32_t>(A) * static_cast<uint32_t>(B);
   D = rotr<32>(A ^ D);

   C += D + 2*static_cast<uint32_t>(C) * static_cast<uint32_t>(D);
   B = rotr<24>(B ^ C);

   A += B + 2*static_cast<uint32_t>(A) * static_cast<uint32_t>(B);
   D = rotr<16>(A ^ D);

   C += D + 2*static_cast<uint32_t>(C) * static_cast<uint32_t>(D);
   B = rotr<63>(B ^ C);
   }

inline void blamka(uint64_t& V0, uint64_t& V1, uint64_t& V2, uint64_t& V3,
                   uint64_t& V4, uint64_t& V5, uint64_t& V6, uint64_t& V7,
                   uint64_t& V8, uint64_t& V9, uint64_t& VA, uint64_t& VB,
                   uint64_t& VC, uint64_t& VD, uint64_t& VE, uint64_t& VF)
   {
   blamka_G(V0, V4, V8, VC);
   blamka_G(V1, V5, V9, VD);
   blamka_G(V2, V6, VA, VE);
   blamka_G(V3, V7, VB, VF);

   blamka_G(V0, V5, VA, VF);
   blamka_G(V1, V6, VB, VC);
   blamka_G(V2, V7, VC, VD);
   blamka_G(V3, V4, V9, VE);
   }

void process_block_xor(secure_vector<uint64_t>& B,
                       size_t offset,
                       size_t prev,
                       size_t new_offset)
   {
   secure_vector<uint64_t> T(128);

   for(size_t i = 0; i != 128; ++i)
      T[i] = B[128*prev+i] ^ B[128*new_offset+i];

   for(size_t i = 0; i != 128; i += 16)
      {
      blamka(T[i+ 0], T[i+ 1], T[i+ 2], T[i+ 3],
             T[i+ 4], T[i+ 5], T[i+ 6], T[i+ 7],
             T[i+ 8], T[i+ 9], T[i+10], T[i+11],
             T[i+12], T[i+13], T[i+14], T[i+15]);
      }

   for(size_t i = 0; i != 128 / 8; i += 2)
      {
      blamka(T[    i], T[    i+1], T[ 16+i], T[ 16+i+1],
             T[ 32+i], T[ 32+i+1], T[ 48+i], T[ 48+i+1],
             T[ 64+i], T[ 64+i+1], T[ 80+i], T[ 80+i+1],
             T[ 96+i], T[ 96+i+1], T[112+i], T[112+i+1]);
      }

   for(size_t i = 0; i != 128; ++i)
      B[128*offset + i] ^= T[i] ^ B[128*prev+i] ^ B[128*new_offset+i];
   }

uint32_t index_alpha(uint64_t random,
                     size_t lanes,
                     size_t segments,
                     size_t threads,
                     size_t n,
                     size_t slice,
                     size_t lane,
                     size_t index)
   {
   return 0;
   }

void process_blocks(secure_vector<uint64_t>& B,
                    size_t t,
                    size_t memory,
                    size_t threads,
                    size_t mode)
   {
   const size_t lanes = memory / threads;
   const size_t segments = lanes / SYNC_POINTS;

   for(size_t n = 0; n != t; ++n)
      {
      for(size_t slice = 0; slice != SYNC_POINTS; ++slice)
         {
         for(size_t lane = 0; lane != lanes; ++lane)
            {
            size_t index = 0;
            if(n == 0 && slice == 0)
               index = 2;

            while(index < segments)
               {
               const size_t offset = lane*lanes + slice*segments + index;

               size_t prev = offset - 1;
               if(index == 0 && slice == 0)
                  prev += lanes;

               BOTAN_ASSERT_NOMSG(128*prev < B.size());
               uint64_t random = B[128*prev];
               size_t new_offset = index_alpha(random, lanes, segments, threads, n, slice, lane, index);

               process_block_xor(B, offset, prev, new_offset);

               index += 1;
               }

            }
         }
      }

   }

}

void argon2(uint8_t output[], size_t output_len,
            const std::string& password,
            const uint8_t salt[], size_t salt_len,
            const uint8_t key[], size_t key_len,
            const uint8_t ad[], size_t ad_len,
            size_t mode, size_t threads, size_t M, size_t t)
   {
   BOTAN_ARG_CHECK(mode == 0 || mode == 1 || mode == 2, "Unknown Argon2 mode parameter");
   BOTAN_ARG_CHECK(output_len >= 4, "Invalid Argon2 output length");
   BOTAN_ARG_CHECK(threads >= 1 && threads <= 128, "Invalid Argon2 threads parameter");
   BOTAN_ARG_CHECK(M >= 8*threads && M <= 8388608, "Invalid Argon2 M parameter");
   BOTAN_ARG_CHECK(t >= 1, "Invalid Argon2 t parameter");

   std::unique_ptr<HashFunction> blake2(new Blake2b);

   const secure_vector<uint8_t> H0 = argon2_H0(*blake2, output_len, password,
                                               salt, salt_len,
                                               key, key_len,
                                               ad, ad_len,
                                               mode, threads, M, t);

   std::cout << "H0 = " << hex_encode(H0) << "\n";

   if(M < 2*SYNC_POINTS*threads)
      M = 2*SYNC_POINTS*threads;

   const size_t memory = (M / (SYNC_POINTS*threads)) * (SYNC_POINTS*threads);
   printf("mtick = %d\n", memory);

   secure_vector<uint64_t> B(memory * 1024/8);

   init_blocks(B, *blake2, H0, memory, threads);
   process_blocks(B, t, memory, threads, mode);

   clear_mem(output, output_len);
   //extract_key(output, output_len, B, memory, threads);
   }

}
