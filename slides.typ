#import "@preview/touying:0.5.5": *
#import "@preview/fletcher:0.5.4" as fletcher: node, edge
#import themes.university: *

#let codeblock(filename) = raw(read(filename), block: true, lang: filename.split(".").at(-1))

#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

#set text(lang: "zh")
#show table: it => align(center, it)

#show: university-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: "Lean 与 AI for Math 简介",
    author: "徐天一",
    institution: "北京国际数学研究中心",
    date: [2025-01-14--2025-01-17],
  )
)

#title-slide()

= 目标

== Lean

- 能读懂 Lean 证明
- 能在 Lean 中形式化简单的数学命题及其证明
- tactic 的原理
  - 能快速学会新的 tactic
- 类型论的基础知识
  - 能在 Lean 中定义数学结构并证明基础结果
- 能快速理解 Lean 的各种报错信息并修改代码

== AI for math
- AI for math 的目标与基本问题
- AI for math 与数学形式化之间的联系
- AI for (formalized) math 的一些进展
- 几个便于使用 Lean 的 AI 工具的介绍


= 为什么要学习 Lean

== 形式化数学的好处

- 用严格的形式语言书写命题及证明，并借助计算机检验其正确性
- 显而易见的好处：避免错误

#speaker-note([
  - Voevodsky 的故事
  - 数学工作者的共识
])

- 隐藏的好处
  - 更清晰的逻辑关系
  - 便于索引及查询（数字化数学的好处）
  - 便于初学者理解数学证明

== 为什么选择 Lean

常见的可用于数学形式化的语言：Coq, Isabelle, Idris, Lean 等

Lean 具有较活跃的社区及庞大的数学库 (mathlib).

Lean 具有强大的元编程能力

== 例子

#{
  set text(16pt)
  codeblock("example/ZeroAdd.lean")
}

#speaker-note([本次课程的目标即为理解这段代码])

== Lean 的安装与配置

- Lean 4 Web: https://live.lean-lang.org/, 免安装的 Lean 环境，适合单文件快速测试
- 本地安装
  - elan: Lean 版本管理器
  - lake: Lean 构建系统
  - lean: Lean 编译器
  - VSCode + Lean 插件: Lean 集成开发环境
  - 安装指南可参考 https://docs.lean-lang.org/lean4/doc/quickstart.html

= 如何用 Lean 书写数学命题

== 命题本身也是数学对象

- 「素数」这一概念应被视为 ℕ 到命题的函数
- 与、或、非等逻辑连接词是命题到命题的函数
- 若 $P : A → "Prop"$, 则“$forall x : A, P x$” 为一个命题

== 例：素数

- 使用现有的定义 $("Nat", +, *)$
- 定义整除：
```lean
def Divides (m n : Nat) : Prop :=
  ∃ k : Nat, n = m * k
```
- 定义素数：
```lean
def Prime (n : Nat) : Prop :=
  ∀ k : Nat, 1 < k → k < n → ¬Divides k n
```
注意这里对条件中合取的处理：→ 是右结合的，即 $p -> q -> r$ 表示 $p -> (q -> r)$.  一般使用这种形式而不使用 $p and q -> r$.

== 例：Euclid 定理

存在无穷多素数

```lean
theorem Euclid : ∀ n : Nat, ∃ p : Nat, p > n ∧ Prime p :=
  sorry
```
`sorry` 表示目前不知道或不关心如何证明


= 如何用 Lean 证明数学命题

== Proof state

- Lean 会记录当前的证明状态，包括已引入的变量和待证明的目标
- 证明状态形如
```lean
n' : N
IH : Nadd Z n' = n'
⊢ Nadd Z (S n') = S n'
```
  - `:` 前的部分是变量名，如 `n'`, `IH`
  - `:` 后的部分是变量类型，如 `N`, `Nadd Z n' = n'`
  - 前提是一种特殊的变量，命题是一种特殊的类型
  - `⊢` 后的部分是待证明的命题
  - 证明状态可以由多个这样的目标组成

== tactic
证明状态的变换

- 常用的 tactic
  - `intro`
  - `rfl`
  - `rewrite` (`rw`)
  - `induction`
  - `apply`
  - `have`

== 例：加法交换律

```lean
theorem Nzero_add : ∀ n, Nadd Z n = n := sorry

theorem NS_add : ∀ m n, Nadd (S m) n = S (Nadd m n) := sorry

theorem Nadd_comm : ∀ m n, Nadd m n = Nadd n m := sorry
```

== `intro`
“引入”一个变量，即将其从待证明的目标中移到条件中

#align(
  center,
  fletcher-diagram(
    node-stroke: 1pt,
    node((0, 0), ```lean
      ⊢ ∀ (n : N), Nadd Z n = n
      ```
    ),
    edge("d", `intro n`, "-|>"),
    pause,
    node((0, 1), ```lean
      n : N
      ⊢ Nadd Z n = n
      ```
    ),
  )
)

== `rfl`
当待证明的目标是一个等式且两边完全相同时，解决这个目标

- `rfl` 是 reflexivity 的缩写
- 在判断“相同”时，定义会被展开，并且 `match` 会被计算

#align(
  center,
  fletcher-diagram(
    node-stroke: 1pt,
    node((0, 0), ```lean
      ⊢ Nadd Z Z = Z
      ```
    ),
    edge("d", `rfl`, "-|>"),
    pause,
    node((0, 1), "（解决）"),
  )
)

- 解释：按 `Nadd` 的定义，第二个参数为 `Z` 时原样返回第一个参数，故 `Nadd Z Z` 视为与 `Z` 相同

== `rewrite`
按照给定的等式 $a = b$ 重写目标，将目标中的 $a$ 全部换成 $b$.

#align(
  center,
  fletcher-diagram(
    node-stroke: 1pt,
    node((0, 0), ```lean
      n' : N
      IH : Nadd Z n' = n'
      ⊢ S (Nadd Z n') = S n'
      ```
    ),
    edge("d", `rewrite [IH]`, "-|>"),
    pause,
    node((0, 1), ```lean
      n' : N
      IH : Nadd Z n' = n'
      ⊢ S n' = S n'
      ```
    ),
  )
)

== `rewrite`
- `rewrite [h₁, h₂, h₃, ...]` 依次使用 `h₁`, `h₂`, `h₃`, ... 重写目标
- 若 `h : a = b`, 但目标中含有 `b`, 则使用 `rewrite [← h]`,
- `rw` 表示在 `rewrite` 之后尝试用 `rfl` 解决目标
- 如果前提 `h₁` 中含有 $a$ 而 `h₂ : a = b`, 则可以用 `rewrite [h₂] at h₁` 来替换
#speaker-note([在实际使用中，`rw` 比 `rewrite` 更为常见，虽然我并不推荐])
- 注意：“$a = b$” 和 “$a$, $b$ 按定义相同”是不同的概念！

== `induction`
对某个变量作归纳；该变量必须本身为归纳类型
#{
  let (a, b1, b2) = ((0, 0), (-1, 1), (1, 1))
  align(
  center,
  fletcher-diagram(
    node-stroke: 1pt,
    node(a, ```lean
      n : N
      ⊢ Nadd Z n = n
      ```
    ),
    edge(a, b1, [`induction n`\ `case Z =>`], "-|>"),
    edge(a, b2, [`induction n`\ `case S n' IH =>`], "-|>"),
    pause,
    node(b1, ```lean
      Nadd Z Z = Z
      ```
    ),
    node(b2, ```lean
      n' : N
      IH : Nadd Z n' = n'
      ⊢ Nadd Z (S n') = S n'
      ```
    ),
  )
)}

- 归纳规则根据类型的定义自动生成

#speaker-note([“归纳规则能够从归纳类型的定义自动生成”这一事实是非平凡的，并且实际上囊括了绝大多数的推理规则])

- `cases` 用于处理不需要用到归纳假设的分类讨论

== `apply`
对当前目标应用某个已证明的命题

#{
  let (a, b1, b2, c) = ((0, 0), (-1, 1), (1, 1), (0, 1))
  align(
  center,
  fletcher-diagram(
    node-stroke: 1pt,
    node(a, ```lean
      p q r : Prop
      h : p → q → r
      ⊢ r
      ```
    ),
    edge(a, c, [`apply h`], "-|>"),
    pause,
    edge(c, b1, "-|>"),
    edge(c, b2, "-|>"),
    node(b1, ```lean
      p q r : Prop
      h : p → q → r
      ⊢ p
      ```
    ),
    node(b2, ```lean
      p q r : Prop
      h : p → q → r
      ⊢ q
      ```
    ),
  )
)}

== `have`
证明某个中间结果

```lean
  have h : 3 * 5 = 15 := by rfl
```

- 如果不加命名，则自动命名为 `this`

== 其他资源
- Lean Games: https://adam.math.hhu.de/#/
  - Natural Number Game: https://adam.math.hhu.de/#/g/leanprover-community/nng4
- Mathematics in Lean: 较为强调在实践中学习的教程 https://leanprover-community.github.io/mathematics_in_lean/index.html
- Theorem Proving in Lean 4: 相对于 MIL 更偏向理论 https://lean-lang.org/theorem_proving_in_lean4/

== 自然数的定义

Peano 公理：
+ $0$ 是自然数
+ 每个自然数 $n$ 都有后继 $S(n)$
+ 自然数是由两个运算的生成的“最小”类型

- 归纳类型是此类定义的一般形式
- 自然数即由两个 constructor 生成
- 假定 $N$ 已被定义，可以写出这两个 constructor 的类型：
  + $Z : N$
  + $S : N -> N$

== 自然数的定义

- 实际上该类型 $N$ 的形态被其全体 constructor 的类型所完全决定, Lean 中也采取此法定义归纳类型

- 对应的 Lean 代码
```lean
inductive N where
  | Z : N
  | S : N → N
```

#speaker-note([这一定义形式上是非直谓的，但实际上可以具体构造出来])

- Lean 会自动生成其归纳规则

== 自然数的归纳规则，简化版
- 分两步理解归纳规则：简化版（非依赖类型版）和完整版
- 非依赖类型版本回答如下问题：若 $A$ 是类型，如何（递归地）定义一个 $f : N -> A$?
  + 选取一个 $h_0$, 令 $f(0) = h_0$
  + 选取一个 $h_S$, 令 $f(S(n)) = h_(S)(n, (f n))$
  - 则 $f$ 就定义好了
- 写出各项目的类型：$h_0 : A$, $h_S : N -> A -> A$, 得出非依赖版的归纳规则：$N_r : A -> (N -> A -> A) -> (N -> A)$
- 该规则应视为不仅具有证明能力，同时具有计算上的能力：$N_(r)(h_0, h_S)(0)$ 与 $h_0$ 按定义完全相同，对 $S(n)$ 的情形也类似
#speaker-note[习题：写出适用于 $N_(r)(h_0, h_S)(S(n))$ 的计算规则]

== 自然数的归纳规则
- 要理解完整版的归纳规则，需要先理解依赖类型
- 将在之后讨论
- 与 `induction` tactic 相对应

== 一些语法上的注意点
- 函数：用 `f x` 表示函数调用 $f(x)$.
  - 好处：多元函数可以自动接受部分参数
    - 这是我们偏向于使用 `p → q → r` 而非 `p × q → r` 的理由
- 缩进：缩进层级在 Lean 中具有语法意义（类似 python）
- 定理和定义的命名
  - 名字空间：所有名字形成一个层级结构
  - 例：`Nat.add_comm`
  - `open` 命令：打开一个名字空间，使其中的名字不需要加上前缀即可使用
  - `namespace` 命令：进入一个名字空间


== 观察到……
- 注意区分命题和它的证明，`p : Prop` 代表 `p` 是一个命题（的陈述），`h : p` 代表 `h` 是 `p` 的证明
- 在 `apply`, `rewrite` 等 tactic 中，需要传入的是一个证明
- `n : N` 代表 $n$ 是一个自然数类型的变量，`h : p` 代表 $h$ 是 $p$ 的证明，而两者的处理方式是相似的

#pause

#align(center, [证明也应视为数学对象！])

= Curry--Howard 同构

==
我们已经观察到将命题和证明视为数学对象所带来的便利，如何系统地给出处理命题和证明的规则？

#pause

如果我们将“命题 $p$”和“$p$ 的全体证明形成的类型”等同起来……

== 积类型 (product type)

积类型 $A times B$ 定义为 $A$, $B$ 中的有序对的全体

#{
  set text(20pt)
  table(
    columns: (auto, auto, auto, auto),
    table.header(table.cell(colspan: 2, $A times B$), table.cell(colspan: 2, $p and q$)),
    [若 $A$, $B$ 是类型], [则 $A times B$ 是类型], [若 $p$, $q$ 是命题], [则 $p and q$ 是命题],
    [若 $x : A$, $y : B$], [则 $(x, y) : A times B$], [若 $p$, $q$ 各有一个证明], [则 $p and q$ 有一个证明],
    [若 $z : A times B$], [则 $z.1 : A$, $z.2 : B$], [若 $p and q$ 有一个证明], [则 $p$, $q$ 各有一个证明],
  )
}

回忆：命题与其全体证明形成的类型等同

#pause

#align(center, [积类型就是命题的合取])

== 和类型 (sum type)

和类型（常称为无交并）$A + B$ 定义为形如 $op("inl") x$ ($x : A$) 和 $op("inr") y$ ($y : B$) 的全体
- 注：$"inl"$, $"inr"$ 是 Lean 中所采用的名字，意为 injection left / injection right

不难想到“和类型”与“析取”相对应

== 函数类型

- 如果 $f$ 为 “$p$ 的证明”到“$q$ 的证明”的函数
- 这样的函数本身可以视作“$p$ 蕴涵 $q$”的证明
- modus ponens 规则可以视作函数调用
  - 例：```lean
      odd_of_prime : ∀ n : Nat, n > 2 → IsPrime n → IsOdd n
      n : Nat
      h : n > 2
      h_p : IsPrime n
      ⊢ odd_of_prime n h h_p : IsOdd n
    ```
    - 注意到 $n$ 也需要作为参数被传入
  - 对应于 `apply` tactic

== 全称量词与 $lambda$-表达式

- 谓词：`IsPrime` 是一个自然数到命题的函数
- 若 $A$ 是一个类型，$P : A -> "Prop"$, 而我们希望证明 $forall x : A, P x$
- 需要表达一类函数，其返回的类型可以依赖于输入的值 (dependently-typed function)
- 依赖函数类型也称为 $Pi$-类型
- 引入一个符号 $"fun" .. => ..$, 若 $m(x)$ 是一个含有 $x$ 的表达式，且有 $x : A tack.r m(x) : P x$, 则 $"fun" x : A => m(x) : forall x : A, P x$
  - 更常用的符号是 $lambda$, 该表达式称为 $lambda$-表达式，相关学科称为 $lambda$-演算
  - Lean 可以视为一种带类型的 $lambda$-演算
- 对应的数学对象：纤维丛的截面

#speaker-note([画图解释])

- 注意到 $p -> q$ 可以视为一种特殊情况，即返回的类型不依赖于输入的值
- 对应于 `intro` tactic
  - 这也解释了 `intro` 既可以用于蕴涵，也可以用于全称量词

== 存在量词

- 若要证明 $exists x : A, P x$, 我们需要构造一个 $a : A$ 和一个 $P a$ 的证明
- 有序对 $(a, b)$, 其中 $b$ 的类型可以依赖于 $a$
- 这样的有序对的类型称为 $Sigma$-类型
- 对应的数学对象：纤维丛的全空间
- 比 $P : A -> "Prop"$ 更一般的是 $P : A -> "Type"$, 其中 $"Type"$ 可以（不严密地）视为所有类型的类型；这样的 $P$ 称为依赖类型；$Pi$-类型和 $Sigma$-类型都可以对这类更一般的依赖类型定义

== 观察、总结与推广
- 类型论有四重解释
  - 作为 $lambda$-演算的类型
  - 作为（构造主义）逻辑
  - 作为范畴论概念
  - 作为代数拓扑概念
- 任何一个合法的 $lambda$-演算表达式同时还是一个命题的证明、一个范畴论中的构造和一个代数拓扑中的构造
- 可以将拓扑中某种熟知的构造迁移到类型论中，etc.

== 对应表
#{
  set text(20pt)
  table(
    columns: (auto, auto, auto, auto),
    table.header([类型论], [逻辑], [范畴论], [代数拓扑]),
    [类型], [命题], [对象], [空间],
    [类型中的值], [证明], [$op("Mor")(1, -)$], [点],
    [依赖类型], [谓词], [\*], [纤维丛],
    [$Pi$-类型], [全称量词], [\*], [纤维丛的截面],
    [$Sigma$-类型], [存在量词], [\*], [纤维丛的全空间],
    [函数类型], [蕴涵], [指数对象 (internal hom)], [映射空间],
    [积类型], [合取], [积对象], [积空间],
    [和类型], [析取], [余积对象], [空间的无交并],
  )
}

#list(
  marker: "*",
  [关于范畴论中对 bundle 的处理可以参见 https://ncatlab.org/nlab/show/Grothendieck+construction],
)

- 例：可以问商空间对应的类型论构造应该是什么样的

== Homotopy type theory

问题：为了定义同伦群，需要找到“空间中的道路”对应的类型论概念

Awodey et al.; Voevodsky （独立提出）：

#pause

#align(center, [$a = b$ 的证明 $<->$ $a$ 到 $b$ 的道路])

在这一观点下，每个类型自然地被解释为一个 ($infinity$-)groupoid.  本次课程不会深究其背后的数学，但这一观点有助于区分 $a = b$ 和 “$a$ 与 $b$ 完全相同”

== HoTT 相关参考资料
- univalent foundations: 一套基于 HoTT 和 univalence axiom 的数学基础 https://github.com/UniMath/UniMath
- HoTT book: https://homotopytypetheory.org/book/, 该网站另有大量 HoTT 相关资料

== `Unit`

具有单个元素的类型/永真的命题
- 有一个不需要任何前提的 constructor
```lean
  inductive Unit where
  | unit : Unit
```
- 是类型范畴中的终对象（任何类型到 `Unit` 都有一个典范映射）
- 如果把 $->$ 视为一个偏序, 则为此偏序下的 top element, 因此也叫做 top type, 记作 $top$ 或 $1$
- 是 $times$ 运算的单位元
- 其命题版本称为 `True`

== `Empty`

空类型/永假的命题
- 没有任何 constructor
```lean
  inductive Empty where
```
- 是始对象
- 是 $->$ 偏序下的 bottom element, 记作 $bot$ 或 $0$
- 是 $+$ 运算的单位元

== algebraic types

$(0, 1, +, times)$ 形成了一个代数结构

- $1 + 1$ 对应布尔类型
- $0 + A tilde.equiv A$
- $1 times A tilde.equiv A$
- $0 times A tilde.equiv 0$
- 甚至可以定义类型的多项式
- 对于有穷类型，有 $|f(A)| = f(|A|)$
- 自然数类型是 $f(A) = 1 + A$ 的最小不动点

更进一步，若把 $->$ 也考虑进去，并把 $A -> B$ 写成 $B^A$, 则也有和数的幂运算相类似的规则

== 关于类型论的一些补充

- 一般类型的四要素
  + 形成规则 (formation rule): 什么情况下可以构造该类型
  + 引入规则 (introduction rule): 如何构造该类型的值
  + 消去规则 (elimination rule): 如何使用一个该类型的值来构造新的值
  + 计算规则 (computation rule): 消去与引入间相互作用的规则
- 对归纳类型而言，形成规则由类型本身具有的参数决定；引入、消去和计算规则由 constructor 决定

== 例：自然数
+ 形成规则：无需前提，`Nat` 总是一个类型
+ 引入规则：`Z` 是一个自然数；若已有 `n` 是自然数，则 `S n` 是自然数
+ 消去规则：若 `P : Nat → Type` 是一个依赖类型，要构造一个 `∀ n : Nat, P n` 中的依赖类型函数
  - 选取 `h_0 : P 0`
  - 选取 `h_S : ∀ n : Nat, P n → P (S n)`
  - 即可得到 `∀ n : Nat, P n` 中的一个函数
  - 特别地，若 `P` 为一个常数 `P n = A`, 就退化为简化版的归纳规则
+ 计算规则：用消去规则定义的函数满足自然的计算性质

== 例：列表
#codeblock("example/List.lean")

== 自然数上的序关系
- 显然可以定义为 `def le (n m : Nat) : Prop := ∃ k, n + k = m`
- 考虑其引入规则
- 可以定义为归纳类型
- ```lean
inductive le (n : Nat) : Nat → Prop
  | refl : le n n
  | step {m} : le n m → le n (succ m)
```
- 这一定义在证明基础性质时往往更便捷

= 如何在 Lean 中处理 Bourbaki 式数学

== 以群的定义为例

如何表达“某个类型 $G$ 是群”？

#codeblock("example/GroupStructure.lean")

更严格地说，`Group G` 对应于 $G$ 上的群结构

== 以群的定义为例

在这个定义中，
```lean
Group.mul : Group.mul {G : Type} (self : Group G) : G → G → G
```

每次使用 `mul` 都需要将 `G` 上的群结构作为一个参数传入

```lean
open Group
theorem mul_inv_cancel (G : Type) (GG : Group G) (a : G) : mul GG a (inv GG a) = one GG := sorry
```

使用这样定义的 `mul_inv_cancel` 时不仅需要传入 `G` 上的群结构，还需要传入类型 `G` 本身，书写时非常不便

== 隐式参数 (implicit parameter)

- 在前面的例子中，`G` 是一个完全多余的参数，因为它可以从 `a` 的类型中推断出来
  - 用 `{G : Type}` 替代 `(G : Type)`
  - 任何参数都可以被定义成隐式的或显式的，没有硬性限制
  - 实践中最好只把“能从其他参数的类型推断出”的参数定义成隐式的，且几乎所有这样的参数都应该定义成隐式的
  - 在调用函数时，可以在显式参数的位置传入 `_`, 要求 Lean 尝试自动生成此处的值
  - 注意 `Group.mul` 等在生成时就将 `G` 标为隐式参数

- ```lean
theorem mul_inv_cancel {G : Type} (GG : Group G) (a : G) : mul GG a (inv GG a) = one GG := sorry
```

== 实例参数 (instance parameter)

- 仍然需要在每次使用时反复传入 $G$ 上的群结构
- `Group G` 的特点：理论上可以有多种，但实际上通常只对一个特定的值讨论
- Lean 为这种情况提供了方便的处理方式
- 将 `structure` 改为 `class`, 并将 `(GG : Group G)` 改为 `[Group G]`
- Lean 会自动从上下文中推断所应该传入的参数

==

#codeblock("example/GroupClass.lean")

== 比较

- 隐式参数和实例参数都提供了一种调用函数时省略一部分参数的机制
- Lean 会在调用时自动计算出应该填入的值
- 在函数内部可以正常使用这些值
- 隐式参数：Lean 会求解这些参数，使得整个表达式符合类型规则
  - 例：`id` 函数
  ```lean
    def id {A : Type} (x : A) : A := x
  ```
  - 考虑表达式 `id 1`: 为了使其符合类型规则，`A` 必须等于 `Nat`
- 实例参数：并没有特别的规则要求使用某个值，但约定某个特殊的值

== 实例推导 (instance inference)

- Lean 在给实例参数填入值时，会考虑当前所有可用的实例并进行推导
- 用 `instance` 命令声明实例；与 `def`/`theorem` 相似，但会被实例推导算法所考虑
- `instance` 命令可以具有输入的实例参数

#codeblock("example/Instance.lean")

- 一个类型为 `Group (Int × Int)` 的实例参数会被自动推导出来
- 这对应数学写作中常见的说法“在乘积空间上的典范群结构”
- `instance` 命令不必局限于一种类型，例如 mathlib 中的 Wedderburn 小定理
```lean
  instance (priority := 100) littleWedderburn (D : Type*) [DivisionRing D] [Finite D] : Field D
```

== 如何让自定义类型支持加法
- 实现对应的 type class
  - ```lean
    class HAdd (α : Type u) (β : Type v) (γ : Type w) where
      hAdd : α → β → γ
  ```
  - `a + b` 会被解释为 `hAdd a b`
  - `add : α → α → α`
- `Add`, `Sub`, `Mul`, `Neg`, `Div`, ...
- 相关定义可以在 `Init.Prelude` 中找到

== 宇宙层级
- Girard 悖论: Russell 悖论的类型论版本
  - 如果允许 `Type : Type` 就会得到
  - 但对 `Type` 的讨论是必须的
- 将 `Type` 分为 $omega$ 层，`Type 0 : Type 1`, `Type 1 : Type 2`, etc.
- 每层 `Type u` 都对所有类型论构造封闭
- 一致性强度：ZFC + 无穷多个不可达基数
- 详细讨论可参考 https://github.com/digama0/lean-type-theory

= 类型论与证明助手

== 类型论作为推理系统

- 由 Curry--Howard 同构可知，证明某命题 $<->$ 构造该命题对应类型的一个值
- 归纳类型和 $Pi$-类型的表达式符合一系列规则
- 大部分数学定义和定理都可以在此系统下进行形式化
- 根据这些规则机械化地检查所写下的表达式是否具有所声明的类型，即验证所写下的证明是否无误 (check)
- 对于一些表达式的子类，还可以自动推导出其所具有的类型 (infer)
- 只要证明这些类型规则具有一些好的性质，即可保证所得到的证明系统是可靠的

== 类型论的实现

- 内核：对完整写出的表达式做类型检验和类型推导
  - 相当简洁，约一千行 C++ 代码
  - "Lean's kernel is small enough that developers can write their own implementation ... it is well within the realm of what is achievable for citizen scientists."
  - 对用户来说非常不友好
- 自动填入隐式参数和实例参数的功能使得用户不必详细写出所有的证明细节，与 Lean 的展开定义功能配合往往能简化证明
- elaboration: 将用户所写的代码转为内核能理解的表达式的过程
  - 隐式参数填充
  - 实例推导
  - 名字解析
  - tactic 执行
  - 信息输出
- elaborator 只影响语言的便利性，不影响正确性
  - 例：`[x₁, x₂, x₃]` 语法
  - 例：`let` 表达式
  - 例：`structure` 命令
  - 例：`#eval` 命令
  - 例：`linarith` tactic
- 元编程：用户可以使用 Lean 的编程能力自行定义 elaborator
  - 以 Lean 作为元语言操作 Lean 自身
  - Lean 编译器的绝大部分代码都是广义的 elaborator, 且是用 Lean 写成的

== 元变量 (metavariable)
elaboration 过程中需要求解的表达式
- 元语言中的变量
- 随着类型检查的进行，元变量的形式会被逐渐细化直至完整求解出来
- 来源：
  - 隐式参数
  - 用 `_` 省略的参数
  - tactic
  - 求解过程中引入

== unification
例：```lean
    def sum {A : Type} (xs : List A) := ...
    def s := sum [2]
  ```
  + 在 `sum [2]` 处引入一个元变量 `?A`
  + 为使表达式 `sum ?A 2` 符合类型规则，须有 `[2] : List ?A`
  + 又已知 `[2] : List Nat`, 根据每个值只能有一个类型的规则，得到约束 `List ?A ≡ List Nat`
  + 解得 `?A := Nat`
  - `sum 2` 会导致 `List ?A ≡ Nat`, 无解

== tactic
- Lean 中的 tactic 也以元变量实现
- 遇到 `by ...` 处，立刻引入一个元变量
- tactic 中可以对元变量进行赋值，或引入新的元变量

== 元编程可以做的事
- 从 Lean 中提取信息
  - 文件梗概
  - 依赖关系
  - tactic 执行前后的 proof state
  - https://github.com/frenzymath/jixia

= mathlib 介绍

== 什么是 mathlib
- 最大的 Lean 数学库
- 约 18 万条定理，9 万个定义
- https://leanprover-community.github.io/mathlib_stats.html
- 涵盖的领域：https://leanprover-community.github.io/mathlib-overview.html
- 1000 个重要数学定理：https://leanprover-community.github.io/1000.html
- 综述文章：https://leanprover-community.github.io/papers/mathlib-paper.pdf

== 使用 mathlib
- 要引入外部依赖，需要创建一个 Lean 项目
- 在命令行中运行 `lake new MyProject math`, 再运行 `lake exe cache get` 下载 mathlib
- 在文件开头加上 `import Mathlib`
- 寻找所需的定理
  - mathlib 中的命名规则（近似）：按照结论 -> 条件的顺序读出定理的类型，省略其中的变量
  - https://leansearch.net/

== 更多常用 tactic
- 填入表达式：`refine`, `exact`
- 处理归纳类型：
  - 引入：`constructor`, `use`, `left`, `right`
  - 消去：`rcases`, `obtain`
- 化简：`simp`, `dsimp`
- 执行判定过程：`decide`
- 解特定目标：`group`, `ring`, `linarith`, `omega`, `field_simp`, `norm_num`
- 组合子：`<;>`, `all_goals`, `try`, `·`

== Lean 中的公理
- Hilbert 风格推演：大量公理，极少推理规则
- 自然推演：大量推理规则
  - 好处：有较好的计算性质
  - 加入公理：失去计算性质
- 排中律
- 外延性

== LEM 与否定
- LEM: 对任意命题 $p$, 有 $p or not p$
  - 在构造主义解释下并不成立
- 以下不依赖 LEM
  - 由 `False` 可以推出一切命题
  - 按照定义，要证明 `¬p` 只需证明 `h : p ⊢ False`
- 以下与 LEM 等价
  - DNE: $not not p -> p$
  - Classical contraposition: $(not p -> not q) -> q -> p$
- `open Classical`
- 相关 tactic: `by_cases`, `by_contra`, `contrapose`

== 外延性
- “相等类型的‘额外’引入规则”
- 函数外延性：对 $f, g : A -> B$, 若对任意 $x : A$ 有 $f(x) = g(x)$, 则 $f = g$
- 作为公理，或作为其他公理的推论得到
- 在 HoTT 中通常作为 univalence axiom 的推论
- 在 Lean 的 type theory 中是商类型存在性的推论
- 命题外延性：若 $p, q : "Prop"$ 且 $p <-> q$, 则 $p = q$
- 相关 tactic: `ext`

== mathlib 中的集合
实际上是谓词的另一种观点

```lean
def Set (α : Type u) := α → Prop
```

- 集合的运算与命题的运算直接对应

== mathlib 中的拓扑
- 由于单侧极限等概念的存在，希望找到一种统一处理的方式
- 使用滤的语言
  - 滤的定义
  - 每种逼近的方式对应一个滤
    - 序列极限：自然数上的余有穷滤
    - 在拓扑空间中趋向于 $x$: $x$ 的邻域滤
    - 单侧极限：邻域滤的限制
  - 直观意义：当前关注的重要的集合，“大的”集合
    - 广义的“几乎处处”

== 滤的基本操作
- 滤的序关系：包含
- 滤的推出：
  若 $f : A -> B$, 则 $f^(-1) : "Set" B -> "Set" A$, 从而 $(f^(-1))^(-1) : "Set"("Set" A) -> "Set"("Set" B)$
- 极限：对 $f : A -> B$, $A$ 上的滤 $l_1$ 和 $B$ 上的滤 $l_2$ 定义
  - $f''(l_1) <= l_2$
  - 例：序列极限 $f : bb(N) -> bb(R)$

== Mathematics in Lean 中的一些例子
- 介绍一些语法和 tactic
- √2 是无理数
- Gauss 整数环

== 相关资料
- https://raw.githubusercontent.com/madvorak/lean4-cheatsheet/main/lean-tactics.pdf
- https://lean-lang.org/doc/reference/latest/

= AI for Math

== 综述
- 希望借助 AI 技术辅助数学的教学和科研
- 有非常广泛的形式
  - 检索
    - 按命题检索
    - 按相似度检索
  - 校验
  - 整理
  - 发现
    - 搜索新证明
    - 发现新概念
    - 提出新猜想
    - 建立新理论
    - Euclid 挑战：给 AI 足够的语料，它能否从中总结出素数的概念

#quote(attribution: [Stefan Banach])[
  A mathematician is a person who can find analogies between theorems; a better mathematician is one who can see analogies between proofs and the best mathematician can notice analogies between theories. One can imagine that the ultimate mathematician is one who can see analogies between analogies.
]


== 自然语言 vs 形式语言
- 自然语言
  - 大量现存语料
  - 便于与人类交互
- 形式语言
  - 文法明确
  - 许多功能不必额外设计，如依赖关系分析、证明正确性检验
  - 杜绝犯错的可能性
- 结合两者的优势

== AI for formalized math 的优势
- 形式化数学的需求：目前的形式化工具需要经过训练才能掌握，且需要数倍甚至数十倍于自然语言数学的时间来完成同等工作
- 对训练 AI 的帮助：相比于自然语言有更精确、更及时的反馈

== 任务定义

#table(
  columns: (auto, auto, auto),
  table.header([], [自然语言], [形式语言]),
  [命题陈述], $S_N$, $S_F$,
  [证明], $P_N$, $P_F$,
)
- 可以加入人类指导、反馈，以自然语言或形式语言写成
- $P_F -> S_F$ 即类型推导
- $S_F -> S_N$, $P_F -> P_N$ 可以被现有的语言模型较好地解决
- $P_N -> S_N$?  常见错误：证明本身没有逻辑问题，但实际证明的命题与声称的命题不同

== 自动形式化 (autoformalization)
- $S_N -> S_F$: 仅翻译陈述
- $S_N + P_N + S_F -> P_F$: 仅翻译证明
- $S_N + P_N -> S_F + P_F$: 完整的自动形式化
  - 批量翻译现存的教科书和论文
  - 新结果的自动审核

== 自动证明 (automated theorem proving)
- $S_F -> P_F$: 自动完成定理证明
  - 证明树搜索
  - 全证明生成 (whole-proof generation)
  - 混合策略：生成完整证明并进行检验，保留到第一个报错信息之前，以此作为证明树节点的一次扩展
  - 递归细化

== 专家系统
- `simp`, `ring` 等也可以视为自动证明系统
- 树搜索：关于 proof state 的 Markov 过程
- `aesop`: 可自定义规则的证明搜索
  - https://github.com/leanprover-community/aesop
  - 自定义规则组
  - 需要人工标注各规则及其“置信度”
  - 完全可信规则：不需要回溯
  - 例：mathlib 中的 `continuity` 使用 `aesop` 实现，用于证明函数的连续性
  - 类型约束起到了限制搜索空间的作用

== 树搜索 + 统计学习
- 分布 $f(t, s)$: 当前状态为 $s$ 时，使用 tactic $t$ 的概率
- 从现有的数据中拟合 $f(t, s)$
- 子任务：前提选择 (premise selection)
  - 分布 $f(A, s)$: 当前状态为 $s$ 时，下一步 tactic 中用到定理 $A$ 的概率
  - 以预测将用到的定理作为辅助输入 (RAG)

== 证明状态估价
- 当前状态 $s$ 能被证明的概率
- 训练 critic model

== 前提选择
- 输出范围是有穷的，且是已知的
- 定理的陈述和当前状态具有某种关联性，且该关联性可以由注意力模型捕捉
- LeanSearch

== tactic 生成
- 以当前状态 + 一些附加信息作为输入
- 生成一条完整的 tactic
- 输出本身可以包含任意表达式，故复杂度可以任意高
- 在 Lean 中处理结构化 tactic 时会遇到一些细节上的困难
- 简化的 tactic language

== 递归细化
- 中间结果预测
- 将证明分为更小的步骤
- 调用其他方法补全中间结果的证明

= AI for Lean 系列工具

== BICMR AI for Math 团队

For the mathematicians, by the mathematicians

在推进 AI for math 的同时，致力于为 Lean 社区贡献高质量的 AI 工具

团队成员（排名不分先后）：董彬，高国雄，居浩成，秦子瀚，姜杰东，高麒，王语同，徐天一，何琬仪，孙梦舟, et al.

== LeanSearch
https://leansearch.net/
- 自然语言的前提选择
- https://arxiv.org/abs/2403.13310
- 将所有 mathlib 中的定理用大语言模型翻译为自然语言
  - 按依赖关系作拓扑排序，将依赖项的翻译作为辅助输入
- 使用开源模型将所有自然语言数据作语义嵌入
- 计算用户查询与数据库中条目的余弦相似度
- 查询扩展：通过大语言模型将用户输入的查询扩展为详细的解释，便于搜索到相似的定理

== Herald
- $(S_F, S_N)$ 数据集
- 关键在于获得大量 $S_F$ 数据
- 通过将 tactic 的中间结果改写为命题形式获得
- 也包含 $(P_F, P_N)$ 数据集
- Herald translator: 命题自动形式化模型
- https://arxiv.org/abs/2410.10878v1

== Lean Agent (under development)
- 基于 Claude 的 Lean 能力和工具调用能力
- 前提选择工具：汇总 mathlib 中定理使用情况的数据并作训练
- 加入后显著提升了 Claude 在本科难度的问题上的表现

#focus-slide([谢谢！])
