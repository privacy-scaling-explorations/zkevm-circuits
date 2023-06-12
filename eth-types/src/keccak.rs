//! Plain keccak256 implementation

use itertools::Itertools;

/// The State is a 5x5 matrix of 64 bit lanes.
type State = [[u64; 5]; 5];

/// The number of rounds for the 1600 bits permutation used in Keccak-256. See [here](https://github.com/Legrandin/pycryptodome/blob/016252bde04456614b68d4e4e8798bc124d91e7a/src/keccak.c#L230)
const PERMUTATION: usize = 24;

/// The Keccak [round constants](https://github.com/Legrandin/pycryptodome/blob/016252bde04456614b68d4e4e8798bc124d91e7a/src/keccak.c#L257-L282)
static ROUND_CONSTANTS: [u64; PERMUTATION] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// The Keccak [rotation offsets](https://github.com/Legrandin/pycryptodome/blob/016252bde04456614b68d4e4e8798bc124d91e7a/src/keccak.c#L232-L255)
static ROTATION_CONSTANTS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// The main keccak object
pub struct Keccak {
    state: State,
    sponge: Sponge,
    scratch: Vec<u8>,
}

impl Default for Keccak {
    fn default() -> Self {
        let security_level = (1088, 512);

        Self {
            state: [[0; 5]; 5],
            // rate & capacity in bytes
            sponge: Sponge::new(security_level.0 / 8, security_level.1 / 8),
            scratch: Vec::new(),
        }
    }
}

impl Keccak {
    /// Take more input bytes to the state
    pub fn update(&mut self, input: &[u8]) {
        let rate = self.sponge.rate;
        // offset for `input`
        let mut offset = 0;

        let scratch_len = self.scratch.len();
        if scratch_len > 0 && scratch_len + input.len() >= rate {
            // concat scratch and input up to the next full `rate`
            offset = rate - scratch_len;
            self.scratch.extend(&input[0..offset]);
            self.sponge.absorb(&mut self.state, &self.scratch);
            self.scratch.truncate(0);
        }

        let chunks_total = (input.len() - offset) / rate;
        if chunks_total != 0 {
            // absorb all chunks
            let tail = offset + (rate * chunks_total);
            self.sponge.absorb(&mut self.state, &input[offset..tail]);
            offset = tail;
        }

        if offset != input.len() {
            // save the remainder
            self.scratch.extend(&input[offset..]);
        }
    }

    /// Returns keccak hash based on current state
    pub fn digest(&mut self) -> Vec<u8> {
        let len = self.scratch.len();
        let padding_total = self.sponge.rate - (len % self.sponge.rate);
        if padding_total == 1 {
            self.scratch.push(0x81);
        } else {
            self.scratch.push(0x01);
            self.scratch.resize(len + padding_total - 1, 0x00);
            self.scratch.push(0x80);
        }
        self.sponge.absorb(&mut self.state, &self.scratch);
        self.scratch.truncate(0);
        self.sponge.squeeze(&mut self.state)
    }
}

#[derive(Default)]
struct KeccakF {}

impl KeccakF {
    fn permutations(&self, a: &mut State) {
        for rc in ROUND_CONSTANTS.iter().take(PERMUTATION) {
            *a = KeccakF::round_b(*a, *rc);
        }
    }

    fn round_b(a: State, rc: u64) -> State {
        let s1 = KeccakF::theta(a);
        let s2 = KeccakF::rho(s1);
        let s3 = KeccakF::pi(s2);
        let s4 = KeccakF::xi(s3);
        KeccakF::iota(s4, rc)
    }

    fn theta(a: State) -> State {
        let mut c: [u64; 5] = [0; 5];
        let mut out: State = [[0; 5]; 5];

        for x in 0..5 {
            c[x] = a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4];
        }

        for (x, y) in (0..5).cartesian_product(0..5) {
            out[x][y] = a[x][y] ^ c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        out
    }

    fn rho(a: State) -> State {
        let mut out: State = [[0; 5]; 5];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out[x][y] = a[x][y].rotate_left(ROTATION_CONSTANTS[x][y]);
        }
        out
    }

    fn pi(a: State) -> State {
        let mut out: State = [[0; 5]; 5];

        for (x, y) in (0..5).cartesian_product(0..5) {
            out[y][(2 * x + 3 * y) % 5] = a[x][y];
        }
        out
    }

    fn xi(a: State) -> State {
        let mut out: State = [[0; 5]; 5];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out[x][y] = a[x][y] ^ (!a[(x + 1) % 5][y] & a[(x + 2) % 5][y]);
        }
        out
    }

    fn iota(a: State, rc: u64) -> State {
        let mut out = a;
        out[0][0] ^= rc;
        out
    }
}

struct Sponge {
    rate: usize,
    capacity: usize,
    keccak_f: KeccakF,
}

impl Sponge {
    fn new(rate: usize, capacity: usize) -> Sponge {
        Sponge {
            rate,
            capacity,
            keccak_f: KeccakF::default(),
        }
    }

    fn absorb(&self, state: &mut State, message: &[u8]) {
        debug_assert!(
            message.len() % self.rate == 0,
            "Message is not divisible entirely by bytes rate"
        );

        let chunks_total = message.len() / self.rate;

        let words: Vec<u64> = Sponge::bits_to_u64_words_le(message);

        for chunk_i in 0..chunks_total {
            let chunk_offset: usize = chunk_i * (self.rate / 8);
            let mut x = 0;
            let mut y = 0;
            for i in 0..(self.rate / 8) {
                let word = words[chunk_offset + i];
                state[x][y] ^= word;
                if x < 5 - 1 {
                    x += 1;
                } else {
                    y += 1;
                    x = 0;
                }
            }
            self.keccak_f.permutations(state);
        }
    }

    fn squeeze(&self, state: &mut State) -> Vec<u8> {
        let mut output: Vec<u8> = vec![];

        let output_len: usize = self.capacity / 2;
        let elems_total: usize = output_len / 8;
        let mut counter: usize = 0;

        'outer: for y in 0..5 {
            for sheet in state.iter().take(5) {
                output.append(&mut sheet[y].to_le_bytes().to_vec());
                if counter == elems_total {
                    break 'outer;
                }
                counter += 1;
            }
        }

        output.resize(output_len, 0);
        output
    }

    fn bits_to_u64_words_le(message: &[u8]) -> Vec<u64> {
        let words_total = message.len() / 8;
        let mut words: Vec<u64> = vec![0; words_total];

        for i in 0..words_total {
            let mut word_bits: [u8; 8] = Default::default();
            word_bits.copy_from_slice(&message[i * 8..i * 8 + 8]);
            words[i] = u64::from_le_bytes(word_bits);
        }
        words
    }
}

/// Convinient method to get 32 bytes digest
pub fn keccak256(msg: &[u8]) -> [u8; 32] {
    let mut keccak = Keccak::default();
    keccak.update(msg);
    keccak.digest().try_into().expect("keccak outputs 32 bytes")
}

#[test]
fn test_keccak256() {
    fn keccak256(msg: &[u8]) -> Vec<u8> {
        let mut keccak = Keccak::default();
        keccak.update(msg);
        let a = keccak.digest();

        let mut keccak = Keccak::default();
        for byte in msg {
            keccak.update(&[*byte]);
        }
        let b = keccak.digest();

        assert_eq!(a, b);

        a
    }
    let pairs = [
        (
            "",
            "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        ),
        (
            "666f6f626172",
            "38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e",
        ),
        (
            "416c6963652077617320626567696e6e696e6720746f20676574207665727920\
            7469726564206f662073697474696e672062792068657220736973746572206f\
            6e207468652062616e6b2c20616e64206f6620686176696e67206e6f7468696e\
            6720746f20646f3a206f6e6365206f7220747769636520736865206861642070\
            656570656420696e746f2074686520626f6f6b20686572207369737465722077\
            61732072656164696e672c2062757420697420686164206e6f20706963747572\
            6573206f7220636f6e766572736174696f6e7320696e2069742c20616e642077\
            6861742069732074686520757365206f66206120626f6f6b2c2074686f756768\
            7420416c69636520776974686f7574207069637475726573206f7220636f6e76\
            6572736174696f6e733f",
            "3ce38e088f876c550dfebe3a1e6a99c2bc06d031106696786482e0b1406235fc",
        ),
    ];
    for (input, output) in pairs {
        let input = hex::decode(input).unwrap();
        let output = hex::decode(output).unwrap();
        assert_eq!(keccak256(&input), output);
    }
}
