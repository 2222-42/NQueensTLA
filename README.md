# NQueensTLA

N*Nの盤面にN個のクイーンを配置する。このとき、どの駒も他の駒に取られないような位置に置いてはいけない。

## Fact

エイトクイーン問題だと、基本解は12種類で、11個には8種類の変形があるが、1つは点対象なので、解の総数は92になることが知られている。

cf:
- https://www.geeksforgeeks.org/n-queen-problem-backtracking-3/
- https://github.com/tlaplus/Examples/blob/master/specifications/N-Queens/Queens.tla

## 4クイーンの例

4*4の盤面だと以下のようなのは解の1つである。

```
{ 0,  1,  0,  0}
{ 0,  0,  0,  1}
{ 1,  0,  0,  0}
{ 0,  0,  1,  0}
```

## 方針

クイーンの配置をn行目のm列目に置かれていると考えると、クイーンの配置は`[1..N -> 1..N]`と表現される。

このうちで解であるものを取り上げる、もしくは解でないものを削っていく。

そこで、specificationを作る順序としては、

1. 他の駒を取りうる、ということを定義する。
2. 解であるとは何かを明示する
3. それを定義する。
4. `n=8`で、定義したものが正しいか、解のケースと解でないケースを入れて確かめる。
5. `n=8`で、解となるような配置を作るアルゴリズムを作る。
6. `n=N`に拡張する。

### 他の駒を取りうる、とは

行は固定なので、以下のいずれかを満たす場合、他の駒を取りうると言える。
- 列が同じか
- 対角線上にあるか。

### 解であるとは

今、配置はすでに済んでいるとする。
この時、解であるとは、どの駒も他の駒に取られないような位置に置いてあることである。

そのため、他の駒を取りうる、ということを定義する必要がある。

### 解となっているかを実例に基づいて確認する

エイトクイーン問題だと、基本解は12種類であるから、それらと、その種類以外のものを1つずつ入れてみて、正しい値が得られるかを、
toolboxのEvaluationでチェックする。

### 解となるような配置を作っていく

1つ入れて、すでに配置済みのクイーンがあれば、それとの関係が他の駒を取りうる関係になっていないように取る。

### Safety Check

なんかTypeInvariant作って、それが補完されているかを確認する

### Liveness Check

`WF_`でチェックする。

### Termination

終わるかどうか確認する
