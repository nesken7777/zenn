---
title: "Lean4でバブルソートを書く"
emoji: "🔄"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4"]
published: false
---

この記事は証明支援系 Advent Calendar 202419日目の記事です

https://adventar.org/calendars/10209

Lean4は定理証明支援系かつ関数型プログラミング言語なんですが、今のところ日本語記事は定理証明に焦点を当ててるものがわりかし体感多い気がします(←ゴミみたいな保険かけ)

なので、Lean4のプログラミング的側面の基本的なところの記事が増えってったらいいなってことで、書いてます

:::message
2024/11/24に`Array.swap`のシグネチャを変更するコミットが入った(https://github.com/leanprover/lean4/pull/6194)ので、nightly(2024-12-05)版を使用しています
:::

:::message
引用するLeanのドキュメントは、日本語訳がある場合はそちらを優先します
:::

## 書く

なんと普通にforで書けます！

```lean4
def bubbleSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  for i in [0:arr.size] do
    for j in [0:arr.size - 1 - i] do
      match Ord.compare arr[j]! arr[j + 1]! with
      |.gt => arr := arr.swapIfInBounds j (j + 1)
      |.lt |.eq => pure ()
  arr
```

驚いただろ

Lean4は関数型言語ではあれど、do記法の中ならかなり手続き的に書くことができます！

具体的には、`else`のない`if`、早期リターン、`for`、`while`、果てには可変変数まで可能です

https://lean-ja.github.io/fp-lean-ja/monad-transformers/do.html

モナドで付け足したい効果が特にない場合であっても、`Id`モナドを使えばいつでもこの記法が使えます
\
\
\
\
\
\
\
\
——————まあこれは茶番だ

## 甘えるな

まあこの記事読んでいる人はそんなことを求めてこれ読んでいるわけではないですもんね^^;

ね^^

さっきの関数は「手続き的に書ける」って特徴が出てましたけど、手続き的に書いてるから関数型っぽくなくてつまんないし、Lean4のメインの強みである境界チェックもできてないし。

というわけでね、さっきの関数をほぼそのまま末尾再帰で書き直します

さっきのは茶番なので軽く説明をすっ飛ばしましたが、ここからは一つ一つ解説します。冗長かも。

まずシグネチャを考えます。型`α`はソートできて、その`α`型の要素の配列を受け取り、ソートした配列を返すので、こう

```
def bubbleSort [Ord α] (arr : Array α) : Array α := _
```

次に外側のループを回すので、こう
```
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α := _
  loop₁ arr 0
```

外側のループは、`i`を増やしながら内側のループを回すので、こう
```
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i : Nat) (j : Nat) : Array α := _
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  loop₁ arr 0
```

内側のループを書いて、こう
```
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i : Nat) (j : Nat) : Array α :=
      if j < arr.size - 1 - i then
        match Ord.compare arr[j] arr[j + 1] with
        |.gt => loop₂ (arr.swap j (j + 1)) i (j + 1)
        |.lt |.eq => loop₂ arr i (j + 1)
      else
        arr
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  loop₁ arr 0
```

これで完成！……って言いたいじゃないですか。ここからが本番だ

この時点で4箇所エラーが出てます
![](/images/articles/lean4-bubblesort/error1.png)

一旦`loop₁`にあるエラーは無視して、indexアクセスと`arr.swap`のエラーを気にします

```
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.19884
inst✝² : Ord α
arr✝¹ : Array α
inst✝¹ : Ord α
arr✝ : Array α
i✝ : Nat
inst✝ : Ord α
arr : Array α
i j : Nat
⊢ j < arr.size
```

```
failed to prove index is valid, possible solutions:
......(中略)
⊢ j + 1 < arr.size
```

これらのエラーが言ってる通り、配列への**普通の**indexアクセスにはindexが配列の範囲内であることの証明が必要になります。

\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\
\

## ちなみに

### `if`で書かないの?

### jを減らす方向に変化させれば

### リストならではの方法で書く

https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Termination.20of.20bubble.20sort.html

### for版を`#print`すると

### for文で証明を取ろうとしても

### 以前の`Array.swap`のシグネチャ

## 小ネタ

Error Lens入れるといいよ

## 戯言

Lean4のシンタックスハイライト早く欲しいよ～

Lean4はコード上じゃ伝わりにくいことがめちゃくちゃあって辛いよ～verso使いたいよ～