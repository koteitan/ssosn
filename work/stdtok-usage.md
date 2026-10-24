# トークン文法の比較

生成と比較（リポジトリのルートで実行）:

```
timeout 1500 python3 work/stdtok_data.py --N 9
timeout 60 python3 work/grammar_check.py grammar_example
timeout 60 python3 work/grammar_check.py work/my_grammar.py --raw
```

候補モジュールは `accept(tokens) -> bool` を定義する。
`tokens` は `('W', 'E1', 'A1')` のような文字列タプル。
`--raw` では `accept(tokens, raw)` を呼ぶ。`raw` は先頭の `(0,0,2,1)` を含む整数タプル。
空列も渡す。例は `grammar_example.py`。

アルファベットは `A0, A1, A2, A3, E1, W`。
このアルファベットの語はすべて上限 `(0,0,2,1,0,2)` より小さい。
比較は候補の結果で枝を刈らず、非標準の語を含む全語を調べる。
不一致はトークン数、次にトークンタプルの辞書順で、それぞれ先頭20件を表示する。

`--N 10` も使用可能。比較対象データは `--data FILE` で変更できる。
生成は既存の `token-laws-check.json` にある標準例を再利用する。
`--no-reuse` で再利用を止められる。
元の `Seq.cut` の計算結果を最大32,768件キャッシュする。
`--no-cut-cache` でキャッシュを止められる。
標準な接頭辞の延長を `std.is_standard` で判定し、非標準な接頭辞の延長は
接頭辞閉性（研究ノート §24）により非標準とする。候補文法は生成に使わない。

## データ形式

`stdtok-N.json`。展開後の JSON が 1 MB を超える場合は `.json.gz`。
生成データは `.gitignore` の対象。

`format` は `stdtok-bits-v1`。
`levels` の各行に `length`, `total`, `standard`, `nonstandard`, `bits_base64` がある。
長さ k の語の番号は、各トークンを上記アルファベットの番号 0..5 に変えた6進数。
ビット列のバイト `code // 8` のビット `code % 8` が標準性を表す。
1 は標準、0 は非標準。末尾のパディングビットは無視する。
この形式で標準と非標準の両方を記録し、空列も長さ0の行に含む。
`stdtok_data.read_data(path)` と `bit_rows(data)` で読み込める。

## N=9 の確認結果

2026-10-24 の生成で、空列を含む全 12,093,235 語のうち、
標準 58,323 語、非標準 12,034,912 語。
長さ9だけでは標準 36,164 語、非標準 10,041,532 語。
生成は約90秒、出力 `stdtok-9.json.gz` は 10,537 バイトだった。
全受理の例文法で全件比較は約2.3秒、`--raw` 付きは約23.7秒。

長さ4以下の全1,555語は、枝刈りなしの `std.is_standard` と一致した。
キャッシュなしの生成データとも同じビット列だった。
既存の標準例17,828件、および各長さのビットの合計数も確認した。
