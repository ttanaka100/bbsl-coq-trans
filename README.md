# Formalization of BBSL with Coq


## このプログラムについて

仕様記述言語BBSLで書かれた仕様をBBSLCoqの仕様へ変換します。Haskell で書かれております。


## コンパイル

コンパイルには unicode-show という Haskell のパッケージが必要なので、取得してください。
そうしたら、bbsl-coq-trans/src へ移動し、以下のコマンドを実行します。
```bash
# build
$ stack ghc Main
```

## 実行
test.bbsl というファイルに変換したい仕様が書かれている場合、bbsl-coq-trans/src へ移動し、以下のコマンドを実行します。

```bash
./Main test.bbsl
```

## エラーチェック
変換対象のbbslファイル内に以下のエラーがあった場合、それを検知します：
- 宣言されていない変数や外部関数が使われる
- 型エラー
- 関数の引数の数が合っていない

## Examples

このフォルダ配下には変換に成功したコードが置いてあります。
Examples/bbsl に変換前のBBSLコードが、Examples/coq に変換後のCoqコードがあります。
また、Examples/error 内のbbslファイルはそれぞれ何らかのエラーが含まれており、エラーチェックの様子を確認できます。


### 参照

- [1] 田中健人, 青木利晃, 川上大介, 千田伸男, 河井達治, & 冨田尭. (2020). 自動運転システムにおける画像を対象とした形式仕様記述言語 BBSL の提案. 研究報告ソフトウェア工学 (SE), 2020(8), 1-8.
- [2] 宇田拓馬. (2021). Coq による BBSL の形式化と検証.
- [3] Thorn, E., Kimmel, S. C., Chaka, M., & Hamilton, B. A. (2018). A framework for automated driving system testable cases and scenarios (No. DOT HS 812 623). United States. Department of Transportation. National Highway Traffic Safety Administration.

