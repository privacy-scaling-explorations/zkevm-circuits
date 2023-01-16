use blake2b::{digest, compress_contract};
use hex::{encode, decode_to_slice};

fn compare_64_digest(msg: &str, key: &str, exp: &str) {
    let mut hash = [0u8; 64];
    digest(&mut hash, msg.as_bytes(), key.as_bytes());
    assert_eq!(encode(&hash), exp);
}

fn compare_compress_contract(input: &str, exp: &str) {
    let mut buffer = [0u8; 213];
    let mut output = [0u8; 64];
    decode_to_slice(input, &mut buffer).expect("Hex input should be correct!");
    compress_contract(&mut output, &buffer);
    assert_eq!(encode(&output), exp);
}

#[test]
#[should_panic(expected = "empty")]
fn digest_hash_empty() {        
    let msg = [8u8; 8];
    let key = [8u8; 8];
    let mut hash = [];
    digest(&mut hash, &msg, &key);      
}

#[test]
#[should_panic(expected = "64 bytes")]
fn digest_hash_above_64() {        
    let msg = [8u8; 8];
    let key = [8u8; 8];
    let mut hash = [0u8; 66];
    digest(&mut hash, &msg, &key);      
}

#[test]
#[should_panic(expected = "64 bytes")]
fn digest_key_above_64() {        
    let msg = [88u8; 8];
    let key = [8u8; 88];
    let mut hash = [0u8; 64];
    digest(&mut hash, &msg, &key);      
}

#[test]
fn digest_no_key_no_msg_64_hash() {        
    let msg = "";
    let key = "";
    let exp = "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce";
    compare_64_digest(msg, key, exp);        
}

#[test]
fn digest_no_key_below_128_msg_64_hash() {        
    let msg = "abc";
    let key = "";
    let exp = "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923";        
    compare_64_digest(msg, key, exp);
}

#[test]
fn digest_no_key_128_msg_64_hash() {        
    let msg = "Wikipedia informs: \"BLAKE-256 and BLAKE-224 use 32-bit words and produce digest sizes of 256 bits and 224 bits, respectively...\"";
    let key = "";
    let exp = "69b9d09bb551ff821a10704848742fa0e78317a824605b95ff18a50047cd8ce977f5694d3231e3f68572d2ecaff601800081002faaac851fb696ddbf704f2ddc";        
    compare_64_digest(msg, key, exp);
}

#[test]
fn digest_no_key_above_128_msg_64_hash() {        
    let msg = 
    "A probis probari, ab improbis improbari aequa laus est. \
     Benefacta male locata malefacta arbitror. \
     Cacatum non est pictum. \
     Corruptissima re publica plurimae leges. \
     Cujusvis hominis est errare, nullius nisi insipientis in errore perseverare. \
     Si vis pacem, para bellum. \
     Ubi culpa est ibi poena subbesse debet.";
    let key = "";
    let exp = "6c34fc4f72d323b45041bf835d28a2d66412447634262c82b4bf125988924dfe6e595cc760ebb73b82be53fd1628dca0f204cd81382adbd7f552579f02de9c38";        
    compare_64_digest(msg, key, exp);
}

#[test]
fn digest_with_key_no_msg_64_hash() {        
    let msg = "";
    let key = "secret";
    let exp = "865aca2ba0b9b941352e4680e14f543d1af37f7a3479304262a5da8c97468d9fe22636bae941d9c7b83b93efc36e82177606c72a1c00af48bb182c69d1f1abc3";
    compare_64_digest(msg, key, exp);        
}

#[test]
fn digest_with_key_below_128_msg_64_hash() {        
    let msg = "example";
    let key = "enigma";
    let exp = "9928ccb6739370244fb01c7421d2198c1223453f56e5bc718c1a0a98443adce2316e59cf06b57f2aad04153f1fb3189f5f2e9bb9998e0209912a3e6855f7c00f";        
    compare_64_digest(msg, key, exp);
}

#[test]
fn digest_with_key_128_msg_64_hash() {        
    let msg = "The BLAKE2b cryptohash function was created by Jean-Philippe Aumasson, Samuel Neves, Zooko Wilcox-O'Hearn, Christian Winnerlein.";
    let key = "classified";
    let exp = "4941cdddf63f3f66efe2665a222728cfc5ca9efadfafc461079033306cf9a94488bdc17de1b609d9cfe28cd9bb12930ffd17de9e408e9b83c3f4228f2a0707c8";        
    compare_64_digest(msg, key, exp);
}

#[test]
fn digest_with_key_above_128_msg_64_hash() {        
    let msg = 
    "De lingua stulta incommoda multa. \
     Definitio fit per genus et differentiam specificam. \
     Domina omnium scientiarum. \
     Juris praecepta sunt haec: honeste vivere, alterum non laedere, suum cuique tribuere. \
     Mens sana in corpore sano. \
     Multum vinum bibere — non diu vivere. \
     Post hoc non est propter hoc. \
     Unus pro omnibus, omnes pro uno.";
    let key = "obscura est";
    let exp = "a2d75c48d1fa23b209b53d97d29cf7b37b7d5c60d4078edec42342772770739c5984f745562e8e81c3f86a1b3d8ca38056362630d13902e1cdd606775e6cce4a";        
    compare_64_digest(msg, key, exp);
}

#[test]
#[should_panic(expected = "final block indicator flag")]
fn compress_contract_vector_3() {        
    let input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000002";
    let exp = "";
    compare_compress_contract(input, exp);   
}

#[test]
fn compress_contract_vector_4() {        
    let input = "0000000048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000001";
    let exp = "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b";
    compare_compress_contract(input, exp);   
}

#[test]
fn compress_contract_vector_5() {    
    let input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000001";
    let exp = "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923";
    compare_compress_contract(input, exp);   
}

#[test]
fn compress_contract_vector_6() {                        
    let input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000000";
    let exp = "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735";
    compare_compress_contract(input, exp);   
}

#[test]
fn compress_contract_vector_7() {                 
    let input = "0000000148c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000001";
    let exp = "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421";
    compare_compress_contract(input, exp);   
}

#[test]
#[ignore]
fn compress_contract_vector_8() {               
    let input = "ffffffff48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e\
    1319cde05b616263000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
    0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000\
    0000000000000000000001";
    let exp = "fc59093aafa9ab43daae0e914c57635c5402d8e3d2130eb9b3cc181de7f0ecf9b22bf99a7815ce16419e200e01846e6b5df8cc7703041bbceb571de6631d2615";
    compare_compress_contract(input, exp);   
}