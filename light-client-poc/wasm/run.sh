rm -rf pkg
wasm-pack build --target web
python3 -m http.server &
open http://localhost:8000
