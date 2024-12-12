---
title: "Lean4でバブルソートを書く"
emoji: "🔄"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4"]
published: false
---

この記事は証明支援系 Advent Calendar 2024 19日目の記事です

https://adventar.org/calendars/10209

Lean4は定理証明支援系かつ関数型プログラミング言語なんですが、今のところ日本語記事は定理証明に焦点を当ててるものがわりかし体感多い気がします(←ゴミみたいな保険かけ)

だけど自分はプログラミング言語としてのLeanがめちゃんこ好きで、プログラミング言語としても流行ってほしいな～て強く思ってます

なので、Leanでのプログラミングの勉強を始めてみたいなと思う人たちに向けて、これを書いてます

対象読者は書かれたコードがなんとなくで読める方です

ただのバブルソートといえどLeanの特徴がいろいろ出て奥深いんですよ！覚悟しておけ

:::message
2024/11/24に`Array.swap`のシグネチャを変更するコミットが入った( https://github.com/leanprover/lean4/pull/6194 )ので、nightly(2024-12-05)版を使用しています
:::

:::message
引用するLeanのドキュメントは、日本語訳がある場合はそちらを優先します
:::

## 書く

なんと普通にforで書けます！

```lean
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

Leanは関数型言語ではあれど、do記法の中ならかなり手続き的に書くことができます！

具体的には、`else`のない`if`、早期リターン、`for`、`while`、果てには可変変数まで可能です。

https://lean-ja.github.io/fp-lean-ja/monad-transformers/do.html

モナドで付け足したい効果が特にない場合であっても、`Id`モナドを使えばいつでもこの記法が使えます。
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

さっきの関数は「手続き的に書ける」って特徴が出てましたけど、手続き的に書いてるから関数型っぽくなくてつまんないし、Leanのメインの強みである境界チェックもできてないし[^1]。

というわけでね、さっきの関数をほぼそのまま末尾再帰で書き直します。

さっきのは茶番なので軽く説明をすっ飛ばしましたが、ここからは一つ一つ解説します。冗長かも。

まずシグネチャを考えます。型`α`は比較できて、その`α`型の要素の配列を受け取り、ソートした配列を返すので、こう

```lean
def bubbleSort [Ord α] (arr : Array α) : Array α := _
```

`Array α`は固定長配列というよりかはRustの`Vec<T>`のようなもので大きさは動的に変化します[^2]

次に外側のループを回すので、こう
```lean
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α := _
  loop₁ arr 0
```

外側のループは、`i`を増やしながら内側のループを回すので、こう
```lean
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
```lean
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

一旦`loop₁`にあるエラーは無視して、indexアクセスと`arr.swap`のエラーを気にします。

### indexが範囲内にあることを証明する

Infoviewに表示されているエラーはこちら

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

エラーにも書いてありますが、`arr[j]!`と書けば範囲外の時にパニックさせたり[^3]、`arr[j]?`と書けば`Option α`として取り出したりすることもできますが、ここは証明で行きましょう！Leanの強みの見せどころです！

まずなぜ`j`と`j + 1`が範囲内にあると確信できるのかと言えば、ifの条件`j < arr.size - 1 - i`を通ったからですね。

じゃあこいつをそのまま証明として取れればいいんだけどな～ってことなんですが、**取れます**。

```lean
if h_index : j < arr.size - 1 - i then
```

このように書けば、`h_index`という名前で`j < arr.size - 1 - i`の証明が取れます。

さらにさらに、Leanはめちゃくちゃ賢いのでこの証明があるだけで`j`も`j + 1`も配列の範囲内だと認めてくれちゃいます！

`arr.swap`も同じ問題なので、こっちのエラーも解決してくれます

なので"証明"といっても、Leanの賢さによって解決されちゃうんですね

現状のエラー状況はこうなります

![](/images/articles/lean4-bubblesort/error2.png)

### `loop₁`が停止することを証明する

さて`loop₁`のエラーはこうなっています

```
fail to show termination for
  bubbleSort.loop₁
with errors
failed to infer structural recursion:
Not considering parameter α of bubbleSort.loop₁:
  it is unchanged in the recursive calls
Not considering parameter #2 of bubbleSort.loop₁:
  it is unchanged in the recursive calls
Cannot use parameter arr:
  the type Array α does not have a `.brecOn` recursor
Cannot use parameter i:
  failed to eliminate recursive application
    bubbleSort.loop₁ (bubbleSort.loop₁.loop₂ arr i 0) (i + 1)


Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            arr i #1
1) 103:6-35   ? ?  ?

#1: arr.size - i

Please use `termination_by` to specify a decreasing measure.
```

Leanでは(`partial def`でも`unsafe def`でもなく)`def`で定義された関数は関数が停止することを保証しなければなりません。このエラーは、「`loop₁`が停止することを証明できなかった」と言っているので、こちら側で停止することを証明する必要があります。

停止することの証明には、`termination_by`を使います。この`termination_by`に、「再帰することで減少するもの」を指定してあげればよいです。

再帰がいつ止まるかと言えば、`i < arr.size`の条件に通らなかった場合なので、`arr.size - i`が0に向かって減少する関係と言えます。

実際Leanも「`arr.size - i`かなー?」って言って諦めてます

> ```
> Could not find a decreasing measure.
> The arguments relate at each recursive call as follows:
> (<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
>            arr i #1
> 1) 11:6-35   ? ?  ?
>
> #1: arr.size - i
> ```

我々も`termination_by arr.size - i`と指示しましょう

```lean
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i : Nat) (j : Nat) : Array α :=
      if h_index : j < arr.size - 1 - i then
        match Ord.compare arr[j] arr[j + 1] with
        |.gt => loop₂ (arr.swap j (j + 1)) i (j + 1)
        |.lt |.eq => loop₂ arr i (j + 1)
      else
        arr
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  termination_by arr.size - i
  
  loop₁ arr 0
```

するとエラー内容が変わります

```
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h✝ : i < arr.size
⊢ (bubbleSort.loop₁.loop₂ arr i 0).size - (i + 1) < arr.size - i
```

「`(bubbleSort.loop₁.loop₂ arr i 0).size - (i + 1) < arr.size - i`の証明をしなさいよ」と言われていますね。Leanはこの証明を諦めたわけです。

これの証明には、`decreasing_by`を使います。

さて、`arr.size - (i + 1) < arr.size - i`なのは当然なのですが、今回示さなければならないのは`(bubbleSort.loop₁.loop₂ arr i 0).size - (i + 1) < arr.size - i`です。`loop₂`が`arr`の大きさを変えることは無いから`arr.size`に書き換えたいんだけどなぁ……

とここで[`rw`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Rw.html)が使えます。`loop₂`によって`arr`の大きさが変わらないこと(`(bubbleSort.loop₁.loop₂ arr i 0).size = arr.size`)を示せば、この`rw`タクティクによってゴールを`arr.size - (i + 1) < arr.size - i`に書き換えて簡単に証明できます。

いったんここまででこういう下書きになります

```lean
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  -- ......(中略)
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by sorry
    rw[loop₂_size_eq]
    sorry
  loop₁ arr 0
```

んーさきに`rw`より下の`sorry`を無くしましょう。

### `arr.size - (i + 1) < arr.size - i`を証明する

この時点でのゴールと持っている仮定は以下のとおりです
```
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h✝ : i < arr.size
loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size
⊢ arr.size - (i + 1) < arr.size - i
```

「いや簡単に証明できそうだけど何の定理がすでに証明されていて使えるのか知らない……！さすがに`n - (m + 1) < n - m`くらいならあるんじゃないか……？！」ってなりますよね。そんなときに使えるのが[`apply?`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/ApplyQuestion.html)です。`apply?`タクティクは証明のために何の定理が使えるのかを探し出してくれます。使ってみましょう

```lean
decreasing_by
  have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by sorry
  rw[loop₂_size_eq]
  apply?
loop₁ arr 0
```

するとInfoviewにこのような表示が出ます
```
Try this: exact Nat.sub_succ_lt_self arr.size i h✝
```
[`Nat.sub_succ_lt_self (a i : Nat) (h : i < a) : a - (i + 1) < a - i`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.sub_succ_lt_self)という定理が使えるようですね。しかも[`apply`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Apply.html)ではなく[`exact`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Exact.html)で行けるようです。ありがたく使わせていただきましょう

```lean
decreasing_by
  have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by sorry
  rw[loop₂_size_eq]
  exact Nat.sub_succ_lt_self arr.size i h✝
```
```
▼ Basic.lean:18:43
expected line break or token
▼ Basic.lean:18:42
unknown identifier 'h'
```

え？( `-´ #)せっかく使ったのになめとんのか

この`h`とやらは`h✝ : i < arr.size`の`h`ですね。Infoviewで変数名に`✝`が付いたものはアクセス不能になってしまったものです。[`rename_i`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/RenameI.html)を使えば名前を付けて復帰できます。

```lean
decreasing_by
  have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by sorry
  rw[loop₂_size_eq]
  rename_i h
  exact Nat.sub_succ_lt_self arr.size i h
```

これで`rw`以後は解決しました。あとは`(bubbleSort.loop₁.loop₂ arr i 0).size = arr.size`を証明すればOKです。

ただこっからが大変です。気合い入れていきましょう。

::::details この先注意！(開くとネタバレ注意)
:::message
`(bubbleSort.loop₁.loop₂ arr i 0).size = arr.size`と設定しているゴールがそもそもよくないです！しかし試行錯誤の過程をそのまま写すためよくないゴールのまま進んでいきます
:::
::::

### `loop₂`が配列の大きさを変えないことを証明する

まずとりあえず`loop₂`を定義に展開しましょう。[`unfold`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Unfold.html)[^4]を使います

```lean
decreasing_by
  have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by
    unfold bubbleSort.loop₁.loop₂
  rw[loop₂_size_eq]
  rename_i h
  exact Nat.sub_succ_lt_self arr.size i h
```
ゴールはこうなります
```
⊢ (if h_index : 0 < arr.size - 1 - i then
      match compare arr[0] arr[0 + 1] with
      | Ordering.gt => bubbleSort.loop₁.loop₂ (arr.swap 0 (0 + 1) ⋯ ⋯) i (0 + 1)
      | Ordering.lt => bubbleSort.loop₁.loop₂ arr i (0 + 1)
      | Ordering.eq => bubbleSort.loop₁.loop₂ arr i (0 + 1)
    else arr).size =
  arr.size
```
`if`が邪魔ですね。`if`のとおり条件分岐をしたい場合は[`split`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Split.html)を使います。

```lean
decreasing_by
  have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by
    unfold bubbleSort.loop₁.loop₂
    split
    case isTrue hlt => sorry
    case isFalse hnlt => sorry
  rw[loop₂_size_eq]
  rename_i h
  exact Nat.sub_succ_lt_self arr.size i h
```

`case isTrue`と`case isFalse`で`hlt : j < arr.size - 1 - i`と`hnlt : ¬j < arr.size - 1 - i`がそれぞれ取れます。

`case isTrue`のゴールはこれ
```
⊢ (match compare arr[0] arr[0 + 1] with
    | Ordering.gt => bubbleSort.loop₁.loop₂ (arr.swap 0 (0 + 1) ⋯ ⋯) i (0 + 1)
    | Ordering.lt => bubbleSort.loop₁.loop₂ arr i (0 + 1)
    | Ordering.eq => bubbleSort.loop₁.loop₂ arr i (0 + 1)).size =
  arr.size
```
`case isFalse`のゴールはこれ
```
⊢ arr.size = arr.size
```

`case isFalse`のゴールは簡単ですね。[`rfl`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Rfl.html)を使って一発です
```lean
case isFalse => rfl
```
`case isTrue`が問題ですね。`Ordering.gt`の場合とそれ以外とで挙動が違います。
というわけでもう一回`split`

```lean
case isTrue =>
  split
  case h_1 => sorry
  case h_2 => sorry
  case h_3 => sorry
```

`case h_1`のゴールを見てみると……

```
⊢ (bubbleSort.loop₁.loop₂ (arr.swap 0 (0 + 1) ⋯ ⋯) i (0 + 1)).size = arr.size
```
うーん……なんか振り出しに戻った感じがする……

また`unfold`する……?いやいや、帰納法を使いましょう。

振り出しに戻ったのは、再帰しているからで、再帰しているなら、帰納法を使って証明するものです。[`induction`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Induction.html)を使った方法で証明をやり直しましょう。

### `loop₂`が配列の大きさを変えないことを証明する₂

……**いやしかし！**`loop₂`は再帰のたびに`i`は変わんないし`j`は増えていきます。つまり引数の中に減るものがないので単純に`induction`を使うことが出来ません。`induction i`でも`induction j`でもないんです。

じゃあなんなのか。そもそも`loop₂`はどうやって停止する再帰になっているかを考えましょう。

`loop₂`は`j < arr.size - 1 - i`を通らなかった場合に止まる再帰であり、`arr.size - 1 - i - j`が減少するわけです。だから

```lean
have loop₂_size_eq : (bubbleSort.loop₁.loop₂ arr i 0).size = arr.size := by
  induction (arr.size - i - 1 - j)
```

と書きたいんですが、「`j`って何？」とコンパイラに言われてしまいます。仕方ないので`(j : Nat)`として引数にしときますか。でもこれじゃ`j`がなんのためにあるのか分かんないので、`j`の役割からしてゴールの`0`を`j`に書き換えておきましょう

```lean
have loop₂_size_eq (j : Nat) : (bubbleSort.loop₁.loop₂ arr i j).size = arr.size := by
  induction (arr.size - i - 1 - j)
```

でこうなるんですが、こう書いたところで、残念ながら都合よく`arr.size - 1 - i - j = 0`や`arr.size - 1 - i - j = n + 1`のような仮定をもらうことができません！

じゃあどうすればこの仮定がもらえるのか……というと、[`generalize`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Generalize.html)を使えばいけます

```lean
have loop₂_size_eq (j : Nat) : (bubbleSort.loop₁.loop₂ arr i j).size = arr.size := by
  generalize hk : arr.size - i - 1 - j = k
  induction k
```

このように書けば、`hk`という名前で`arr.size - 1 - i - j = 0`や`arr.size - 1 - i - j = n + 1`が仮定として使えるようになります。

現状こうなります

```lean
have loop₂_size_eq (j : Nat) : (bubbleSort.loop₁.loop₂ arr i j).size = arr.size := by
  generalize hk : arr.size - i - 1 - j = k
  induction k <;> unfold bubbleSort.loop₁.loop₂
  case zero => sorry
  case succ n ih => sorry
```

[`<;>`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/SeqFocus.html)を使って`induction`によって生まれる2つのゴールの両方に`unfold`をあてています。どちらも`unfold`することには変わりないので。

まず`case zero`から

```lean
case zero =>
  split
  case isTrue hlt => sorry
  case isFalse hnlt => rfl
```

`case isFalse`はさっきと同じなのでパパっと`rfl`しときましょう。

`case isTrue`なんですが、仮定に
```
hk : arr.size - 1 - i - j = 0
hlt : j < arr.size - 1 - i
```
の二つがあります。`arr.size - 1 - i - j = 0`なのに`j < arr.size - 1 - i`なのはおかしな話です。矛盾を示しましょう。

ただ単に[`contradiction`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Contradiction.html)を使おうとしても何かしらの真逆の仮定は持ち合わせていないので、失敗しちゃいます。`arr.size - 1 - i - j ≠ 0`を作ってから`contradiction`しましょう。

```lean
case isTrue hlt =>
  have h_ne_z : arr.size - 1 - i - j ≠ 0 := by sorry
  contradiction
```

さて`h_ne_z`をどうするかなんですが、まあ分かんなかったらとりあえず`apply?`しとけばいいんですよ

```lean
case isTrue hlt =>
  have h_ne_z : arr.size - 1 - i - j ≠ 0 := by apply?
  contradiction
```
```
Try this: exact Nat.sub_ne_zero_iff_lt.mpr hlt
```
定理[`Nat.sub_ne_zero_iff_lt {n m : Nat} : n - m ≠ 0 ↔ m < n`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.sub_ne_zero_iff_lt)ありますね。使います
```lean
case isTrue hlt =>
  have h_ne_z : arr.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hlt
  contradiction
```
これで`case isTrue`の証明が完了したので、`case zero`は証明完了です！うまくいっていますね
```lean
case zero =>
  split
  case isTrue hlt =>
    have h_ne_z : arr.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hlt
    contradiction
  case isFalse hnlt => rfl
```
残るは`case succ`ですね

```lean
case succ n ih =>
  split
  case isTrue hlt => sorry
  case isFalse hnlt => rfl
```

`case isFalse`は、一応`hk : arr'.size - 1 - i - j = n + 1`で`hnlt : ¬j < arr'.size - 1 - i`なのは矛盾しているのですが、`rfl`って言った方が簡単なので`rfl`って言ってます

今回の`case isTrue`は別に持っている仮定に矛盾がないので、前回と同じように`split`

```lean
case isTrue hlt =>
  split
  case h_1 => sorry
  case h_2 => sorry
  case h_3 => sorry
```

問題の`case h_1`は……
```
⊢ (bubbleSort.loop₁.loop₂ (arr.swap j (j + 1) ⋯ ⋯) i (j + 1)).size = arr.size
```

ふむ。まあまあまあ今回は帰納法でやってるんで帰納ケースの仮定が――――――

```
ih : arr.size - 1 - i - j = n → (bubbleSort.loop₁.loop₂ arr i j).size = arr.size
hk : arr.size - 1 - i - j = n + 1
```

……**使えない！！！！** 使えないんだが！？

まず`ih`を使うのに必要な前提も満たせないし`ih`の結論が`(arr.swap j (j + 1) ⋯ ⋯)`じゃなくて`arr`に対してしか使えない！

困った……一体どうすれば…………

うーーーーーーーーーーーーーーーーーーーーーーーーーーん

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
はい。

ネタバレ注意！のところに書いたとおり、問題なのはゴールが具体的すぎることです。

出てくる変数をもう少し一般化して、帰納法の仮定として使えるようにしておきましょう。

でも特に当然だけど大事なのは、再帰によって次に引数として渡される配列は **`Array.swap`によって変化している可能性がある** ということです。これが原因でさっきは失敗していたわけです。よって左辺(`(bubbleSort.loop₁.loop₂ arr i j).size`)の`arr`と右辺(`arr.size`)の`arr`は別物として扱わなければなりません。ここからは左辺の配列を`arr'`としておきましょう。

ただし、引数として渡される`arr'`の大きさともともとの`arr`の大きさが違うことはないということ抜きには証明できません。

よって新しく考える定理はこうなります:「任意の`arr'.size = arr.size`な`arr'`, `arr`と自然数`i`,`j`について、`(bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`」

というわけで書き直したゴールはこうなります
```lean
have loop₂_size_eq (arr' arr : Array α) (i j : Nat) (h_size : arr'.size = arr.size) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by sorry
```

また証明やり直しです(^-^)/

### `loop₂`が配列の大きさを変えないことを証明する₃

ただちょっと待って！このままでは帰納ケースで得られる仮定が`ih : arr'.size - 1 - i - j = n → (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`であり、さっきから躓いている`case h_1`のときの
```
⊢ (bubbleSort.loop₁.loop₂ (arr'.swap j (j + 1) ⋯ ⋯) i (j + 1)).size = arr.size
```
というゴールは`arr'`は`(arr'.swap j (j + 1) ⋯ ⋯)`ですし、`j`は`j + 1`になってるので仮定を使って対応できません。

これに対応するため、`induction`には`generalizing`構文を使ってもう少し強力な仮定にします。

とりあえず`arr'`と`i`と`j`を、`generalizing`を使って一般化しておきましょう[^5]

```lean
have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.size) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
  generalize hk : arr'.size - 1 - i - j = k
  induction k generalizing arr' i j <;> unfold bubbleSort.loop₁.loop₂
  case zero => sorry
  case succ n ih => sorry
```

これで帰納ケースで得られる仮定が`ih : ∀ {arr' : Array α} {i j : Nat}, arr'.size = arr.size → arr'.size - 1 - i - j = n → (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`になってくれました！

またやり直しか…はあ……と思ってるかもしれませんが、安心してください！今までやってきた証明を多少変えるだけです

まず`case zero`ですが、`case isFalse`の際のゴールが`arr'.size = arr.size`と少し変わっています。仮定`h_size`を持っているので、`exact`しましょう
```lean
case zero =>
  split
  case isTrue hlt =>
    have h_ne_z : arr'.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hlt
    contradiction
  case isFalse hnlt => exact h_size
```
さて`case succ`
```lean
case succ n ih =>
  split
  case isTrue hlt => sorry
  case isFalse hnlt => sorry
```
`case isFalse`は`exact h_size`でも証明できますが、一応矛盾してるし矛盾を示しません?

定理[`Nat.lt_of_sub_eq_succ {m n l : Nat} (h : m - n = l.succ) : n < m`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.lt_of_sub_eq_succ)もあるので、簡単です

```lean
case isFalse hnlt =>
  have : j < arr'.size - 1 - i := by exact Nat.lt_of_sub_eq_succ hk
  contradiction
```

問題は`case isTrue`です。とりあえず`split`
```lean
case isTrue hlt =>
  split
  case h_1 => sorry
  case h_2 => sorry
  case h_3 => sorry
```

さて……問題の`case h_1`
```
⊢ (bubbleSort.loop₁.loop₂ (arr'.swap j (j + 1) ⋯ ⋯) i (j + 1)).size = arr.size
```

あの時とは違って、今の我々には仮定`ih : ∀ {arr' : Array α} {i j : Nat}, arr'.size = arr.size → arr'.size - 1 - i - j = n → (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`を持っています！これを使って解決しましょう！

今の仮定`ih`は"任意の"`arr'`と`i`と`j`について言える話なので、これらは何にするか自分で決められるわけです。今回の場合は`arr'`には`(arr'.swap j (j + 1))`を、`i`には`i`を、`j`には`(j + 1)`を指定します

ただ少し面倒くさくなっている所があって、その自分で決めた`arr'`、`i`、`j`(今回の場合`arr'.swap j (j + 1)`、`i`、`(j + 1)`)が`arr'.size = arr.size`や`arr'.size - 1 - i - j = n`を満たすことも証明しとかなければいけません。

`ih`の結論と今回のゴールが一致しているので、`apply ih`ができます

```lean
case h_1 =>
  apply ih
  case h_size => sorry
  case hk => sorry
```

`case h_size`のゴール
```
⊢ (arr'.swap j (j + 1) ⋯ ⋯).size = arr.size
```
と`case hk`のゴール
```
⊢ (arr'.swap j (j + 1) ⋯ ⋯).size - 1 - i - (j + 1) = n
```
が現れました。めんどっち～

ただどっちも`(arr'.swap j (j + 1) ⋯ ⋯).size`が出ているけど、これって`arr'.size`と変わりませんよね。[`Array.size_swap`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Array/Basic.html#Array.size_swap)という定理もあるので、先に持っておきましょう

```lean
case h_1 =>
  apply ih
  have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
  case h_size => sorry
  case hk => sorry
```

`case h_size`の方は[`Eq.trans`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Eq.trans)(推移律)で証明できます。`case hk`の方は一旦`rw`しておきましょう

```lean
case h_1 =>
  have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
  apply ih
  case h_size => exact h_size_swap.trans h_size
  case hk =>
    rw[h_size_swap]
```

さて`case hk`のゴールは`⊢ arr'.size - 1 - i - (j + 1) = n`となりましたが、ここで最強タクティク[`omega`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Omega.html)が使えます！`omega`は自然数や整数の計算なら結構なんでもありに自動で証明してくれるタクティクです。これくらいの証明なら`omega`ぶっぱで解決します

```lean
case h_1 =>
  have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
  apply ih
  case h_size => exact h_size_swap.trans h_size
  case hk =>
    rw[h_size_swap]
    omega
```

……いやーせっかくだし手で証明しません？^^;

[`calc`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Calc.html)を使って`=`で繋いでいきます。

まず証明したい等式の左辺から
```lean
case hk =>
  rw[h_size_swap]
  calc arr'.size - 1 - i - (j + 1)
```

`hk : arr'.size - 1 - i - j = n + 1`があるのでそれにあわせて変形し、
```lean
case hk =>
  rw[h_size_swap]
  calc arr'.size - 1 - i - (j + 1)
    _ = (arr'.size - 1 - i - j) - 1 := rfl
```

[`Nat.sub_eq_of_eq_add {a b c : Nat} (h : a = c + b) : a - b = c`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.sub_eq_of_eq_add)があるのでこれで証明完了です

```lean
case hk =>
  rw[h_size_swap]
  calc arr'.size - 1 - i - (j + 1)
    _ = (arr'.size - 1 - i - j) - 1 := rfl
    _ = n := Nat.sub_eq_of_eq_add hk
```

これでようやく`case h_1`を乗り越えました！

あとは`case h_2`と`case h_3`です

ゴールはどちらも
```
⊢ (bubbleSort.loop₁.loop₂ arr' i (j + 1)).size = arr.size
```
なんですが、結局同じように`arr'.size - 1 - i - (j + 1) = n`の証明が必要になりそうですね。

といわけでさっき`calc`で証明したのを`h_eq_n`として`split`の前にとっておきましょう

これさえとれればあとは簡単なので、説明も省きます

```lean
case isTrue hlt =>
  have h_eq_n : arr'.size - 1 - i - (j + 1) = n := by
    calc arr'.size - 1 - i - (j + 1)
    _ = (arr'.size - 1 - i - j) - 1 := rfl
    _ = n := Nat.sub_eq_of_eq_add hk
  split
  case h_1 =>
    have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
    apply ih
    case h_size => exact h_size_swap.trans h_size
    case hk =>
      rw[h_size_swap]
      exact h_eq_n
  case h_2 =>
    apply ih
    case h_size => exact h_size
    case hk => exact h_eq_n
  case h_3 =>
    apply ih
    case h_size => exact h_size
    case hk => exact h_eq_n
```

これで`case isTrue`を乗り越えたので、ようやく`loop₂_size_eq`の証明が完了しました……！

これで`decreasing_by`の証明が……！？まだ終わりませ～ん^^

`loop₂_size_eq`のシグネチャがだいぶ変わったので、なんの`arr'`と`arr`と`i`と`j`で`rw`したいのか指定しなければいけません。

もともと`(bubbleSort.loop₁.loop₂ arr i 0).size = arr.size`を証明したかったわけなので、引数`arr'`,`arr`には`arr`を、引数`i`には`i`を、引数`j`には`0`を、そして`h_size`には`rfl`を指定します。

```lean
decreasing_by
  have loop₂_size_eq (arr' arr : Array α) (i j : Nat) (h_size : arr'.size = arr.size) :
    (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := /- 省略 -/
  rw[loop₂_size_eq arr arr i 0 rfl]
  rename_i h
  exact Nat.sub_succ_lt_self arr.size i h
```

これで本当に`decreasing_by`の証明が完了しました！

そしてこれにより……！`bubbleSort`の定義が……！完了しました！！！！！

## まとめ・コード全体を見る

では完成したバブルソートのコード全体を見てみましょう

```lean
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i : Nat) (j : Nat) : Array α :=
      if h_index : j < arr.size - 1 - i then
        match Ord.compare arr[j] arr[j + 1] with
        |.gt => loop₂ (arr.swap j (j + 1)) i (j + 1)
        |.lt |.eq => loop₂ arr i (j + 1)
      else
        arr
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq (arr' arr : Array α) (i j : Nat) (h_size : arr'.size = arr.size) :
      (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
      generalize hk : arr'.size - 1 - i - j = k
      induction k generalizing arr' i j <;> unfold bubbleSort.loop₁.loop₂
      case zero =>
        split
        case isTrue hlt =>
          have h_ne_z : arr'.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hlt
          contradiction
        case isFalse hnlt => exact h_size
      case succ n ih =>
        split
        case isTrue hlt =>
          have h_eq_n : arr'.size - 1 - i - (j + 1) = n := by
            calc arr'.size - 1 - i - (j + 1)
            _ = (arr'.size - 1 - i - j) - 1 := rfl
            _ = n := Nat.sub_eq_of_eq_add hk
          split
          case h_1 =>
            have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
            apply ih
            case h_size => exact h_size_swap.trans h_size
            case hk =>
              rw[h_size_swap]
              exact h_eq_n
          case h_2 =>
            apply ih
            case h_size => exact h_size
            case hk => exact h_eq_n
          case h_3 =>
            apply ih
            case h_size => exact h_size
            case hk => exact h_eq_n
        case isFalse hnlt =>
          have : j < arr'.size - 1 - i := by exact Nat.lt_of_sub_eq_succ hk
          contradiction
    rw[loop₂_size_eq arr arr i 0 rfl]
    rename_i h
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0
```

全体で55行！バブルソート1つで55行！頑張りましたね！まあ2/3ほど証明に使ってますが

ただ見誤らないで！55行もするのは甘えずに証明付きで書くことを頑張ったからであって、「Leanだとバブルソートに55行も書かされる」のではありません！

他の大体の言語だと実行時エラーだったり未定義動作だったりOptionを返したりするindexアクセスを「必ずindexが範囲内にある」って保証したりとか、他の大体の言語だと無限ループする関数と必ず停止する関数の区別がつかないのを「この関数は必ず停止する」って言いきったりとか[^6]、**甘えなければ**Leanでそういうことができるんです。

別に甘えてもいいんです。証明がだるかったら`def`に`partial`付けたっていいし、何なら`for`で書いたっていいんです。`arr[i]!`も使ったっていいんです。



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

折りたたむやつ使うとページ内検索に支障が出るのでここに補足情報全部書きます

### `if`で書かないの?

### 結局indexアクセスと`arr.swap`の証明ってどうなってるの?

### `loop₂`はなんで停止することの証明が要らなかったの?

### どうやってそうなってることを知ったの?

### `[Inhabited α]`と`[Ord α]`って何?

### for版を`#print`すると

### for文で証明を取ろうとしても

### 以前の`Array.swap`のシグネチャ

## 小ネタ

Error Lens入れるといいよ

## 戯言

Leanのシンタックスハイライト早く欲しいよ～

エラー表示用のコードブロックも欲しいよ～

Leanはコード上じゃ伝わりにくいことがめちゃくちゃあって辛いよ～verso使いたいよ～

[^1]:四苦八苦した挙句諦めました……

[^2]:[Vector](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Vector/Basic.html)はそれはそれで別であります

[^3]: 代償?として`[Inhabited α]`が必要 \
      forを使った関数の方はこっちを使ってた

[^4]:[`dsimp`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Dsimp.html)はなぜか何も展開してくれませんでした……

[^5]:ちなみに`arr`も`generalizing`してもいいですし`i`は別に`generalizing`しなくてもいいです。あと「使えない！」って騒いでた時も実は`j`だけは`generalizing`できます

[^6]:でも`partial`はkokaの`div`エフェクトみたいに伝播しないからミスリーディング味ある