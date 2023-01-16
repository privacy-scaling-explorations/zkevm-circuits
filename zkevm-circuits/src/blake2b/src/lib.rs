use core::panic;

const IV: [u64; 8] = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 
    0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179];

const SIGMA:[[usize; 16]; 10] = [ 
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]];

fn g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);

    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);

    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16); 
    
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

fn compress(h: &mut [u64; 8], m: &[u64; 16], t: u128, f: bool, r: u32) {
    let mut v = [0u64; 16];
    
    for i in 0..8 {       
        v[i] = h[i];
        v[i + 8] = IV[i];
    }

    v[12] ^= t as u64;
    v[13] ^= (t >> 64) as u64;
    
    if f { v[14] ^= 0xFFFF_FFFF_FFFF_FFFF; }

    for i in 0..(r as usize) {
        let s = &SIGMA[i % 10];

        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);

        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

fn load_bytes(d: &mut [u8], s: &[u64]) {
    if s.len() * 8 < d.len() {
        panic!("Not enough data in the source slice!");
    }
    
    let q = d.len() / 8;
    for i in 0..q {
        d[8 * i..][..8].copy_from_slice(&s[i].to_le_bytes());
    }

    let b = d.len() - 8 * q;
    if b == 0 { return; }

    let mut l = s[q];
    for i in 8 * q..d.len() {
        d[i] = l as u8;
        l >>= 8;    
    }
}

fn save_bytes(d: &mut [u64], s: &[u8]) {
    if d.len() * 8 < s.len() {
        panic!("Not enough memory in the destination slice!");
    }

    let q = s.len() / 8;
    for i in 0..q {
        d[i] = u64::from_le_bytes(s[8 * i..][..8].try_into().unwrap());
    }

    let b = s.len() - 8 * q;
    if b == 0 { return; }

    let (mut l, mut p) = (0u64, 0);
    for i in 8 * q..s.len() {
        l |= (s[i] as u64) << p;
        p += 8;
    }

    d[q] = d[q] & (0xFFFF_FFFF_FFFF_FFFF << (8 * b)) | l;
}

pub fn compress_contract(output: &mut [u8; 64], input: &[u8; 213]) {
    if input[212] > 1 {
        panic!("Incorrect final block indicator flag!");
    }

    let mut h = [0u64; 8];
    save_bytes(&mut h, &input[4..68]);
    let mut m = [0u64; 16];
    save_bytes(&mut m, &input[68..196]);
    
    let t = u128::from_le_bytes(input[196..212].try_into().unwrap());
    let f = input[212] == 1;
    let r = u32::from_be_bytes(input[0..4].try_into().unwrap()); 

    compress(&mut h, &m, t, f, r);
    load_bytes(output, &h);
}

pub fn digest(hash :&mut [u8], msg: &[u8], key: &[u8]) {
    if (hash.len() == 0) || (hash.len() > 64) {
        panic!("Hash cannot be empty or longer than 64 bytes!");
    }
    if key.len() > 64 {
        panic!("Key cannot be longer than 64 bytes!");
    }

    const R: u32 = 12;
    let mut h = IV;

    h[0] ^= 0x0101_0000 ^ ((key.len() as u64) << 8) ^ (hash.len() as u64);

    let mut t = 0u128;
    let s = key.len() > 0;
    let e = msg.len() == 0;
    let mut b = [0u64; 16];

    if s { 
        save_bytes(&mut b, key);
        t += 128;
    }

    if s || e  { 
        compress(&mut h, &b, t, e, R); 
    }              

    if !e {
        let mut n = msg.len() / 128;
        if msg.len() % 128 == 0 { n -= 1; }

        for i in 0..n {
            t += 128;
            save_bytes(&mut b, &msg[128 * i..][..128]);
            compress(&mut h, &b, t, false, R);   
        }

        b = [0u64; 16];
        t += (msg.len() - 128 * n) as u128;
        save_bytes(&mut b, &msg[128 * n..]);
        compress(&mut h, &b, t, true, R);
    }
 
    load_bytes(hash, &h);
}