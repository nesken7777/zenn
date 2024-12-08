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

なので、Leanでのプログラミングの勉強を始めてみたいなと思う人たちに向けて、これを書いてます

ただのバブルソートといえどLeanの特徴がいろいろ出て奥深いんですよ！覚悟しておけ

:::message
2024/11/24に`Array.swap`のシグネチャを変更するコミットが入った(https://github.com/leanprover/lean4/pull/6194)ので、nightly(2024-12-05)版を使用しています
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

まずシグネチャを考えます。型`α`はソートできて、その`α`型の要素の配列を受け取り、ソートした配列を返すので、こう

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

### indexが範囲内にあるかどうかの証明

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

実際Leanも`arr.size - i`かなー?って言って諦めてます

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
`Nat.sub_succ_lt_self (a i : Nat) (h : i < a) : a - (i + 1) < a - i`という定理が使えるようですね。ありがたく使わせていただきましょう

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
      case isTrue => sorry
      case isFalse => sorry
    rw[loop₂_size_eq]
    rename_i h
    exact Nat.sub_succ_lt_self arr.size i h
```

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

また`loop₂`を展開したところでまた同じ問題に出くわすだけだし余計にややこしくなるだけだし……

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
はい。

ネタバレ注意！のところに書いたとおり、問題なのはゴールが具体的すぎることです。

振り出しに戻ったのは、再帰しているからで、再帰しているなら、帰納法を使って証明するものです。

出てくる変数をいろいろ一般化して、帰納法の仮定として使えるようにしておきましょう。

でも特に当然だけど大事なのは、引数として渡される`arr`の大きさが変わってはいけないということです。

よって新しく考える定理はこうなります:「任意の`arr'.size = arr.size`な`arr'`, `arr`と自然数`i`,`j`について、`(bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`」

Leanはそこで使う`arr'`,`arr`,`i`,`j`については証明中にいろいろ推論してくれるので、暗黙パラメータにしておきます。暗黙パラメータにするには、中括弧`{}`を使います。

というわけで書き直したゴールはこうなります
```lean
have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.size) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by sorry
```

証明やり直しです(^-^)/

じゃあまず帰納法使いたい訳なんですが、なんですが、`loop₂`は再帰のたびに`arr'`は変わるし`i`は変わんないし`j`は増えていきます。つまり単純に[`induction`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Induction.html)を使うことが出来ません。そもそも`loop₂`はどうやって停止する再帰になっているかと言えば、`j < arr.size - 1 - i`を通らなかった場合に止まる再帰であり、`arr.size - 1 - i - j`が減少するわけです。だから
```lean
have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.size) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
  induction (arr'.size - 1 - i - j)
```

と書きたいんですが、都合よく`arr'.size - 1 - i - j = 0`や`arr'.size - 1 - i - j = n + 1`のような仮定をもらうことができません！

じゃあどうすればこの仮定がもらえるのか……というと、[`generalize`タクティク](https://lean-ja.github.io/lean-by-example/Reference/Tactic/Generalize.html)を使えばいけます

```lean
have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.ize) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
  generalize hk : arr'.size - 1 - i - j = k
  induction k
```

このように書けば、`hk`という名前で`arr'.size - 1 - i - j = 0`や`arr'.size - 1 - i - j = n + 1`が仮定として使えるようになります。

ただちょっと待って！先のことを一旦考えます。このままでは帰納ケースで得られる仮定が`arr'.size - 1 - i - j = n → (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size`であり、以前遭遇した`case h_1`のときの
```
⊢ (bubbleSort.loop₁.loop₂ (arr'.swap j (j + 1) ⋯ ⋯) i (j + 1)).size = arr.size
```
というゴールは`arr'`ではなく`arr'.swap`した後の配列ですし、`j`は`j + 1`になってるので仮定を使って対応できません。

これに対応するため、`induction`には`generalizing`構文を使ってもう少し強力な仮定にします。

とりあえず`arr'`と`i`と`j`を、`generalizing`を使って一般化しておきましょう[^5]

現状こうなります

```lean
have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.size) :
  (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
  generalize hk : arr'.size - 1 - i - j = k
  induction k generalizing arr' i j <;> unfold bubbleSort.loop₁.loop₂
  case zero => sorry
  case succ n ih => sorry
```

[`<;>`](https://lean-ja.github.io/lean-by-example/Reference/Tactic/SeqFocus.html)を使って`induction`によって生まれる2つのゴールの両方に`unfold`をあてています。どちらも`unfold`することには変わりないので。

まず`case zero`から

```
case zero =>
  split
  case isTrue hlt => sorry
  case isFalse hnlt => sorry
```

まず`case isTrue`なんですが、仮定に
```
hk : arr'.size - 1 - i - j = 0
hlt : j < arr'.size - 1 - i
```
の二つがあります。`arr'.size - 1 - i - j = 0`なのに`j < arr'.size - 1 - i`なのはおかしな話です。矛盾を示しましょう。

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

[^5]:ちなみに`i`は別に`generalizing`しなくていいです