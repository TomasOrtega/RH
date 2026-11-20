import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Exists

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

/- English proof (translation)
Take `⟨α, β, hα, hβ, hf, hg, -⟩` from `hs`. Break down `mem_of_ratDiv_ne_zero hW with h | h` into its components or cases. Conclude with `isProjVarF_of_mem_divSupp hV hα hf h`. Conclude with `isProjVarF_of_mem_divSupp hV hβ hg h`.
-/
theorem multi_isProjVarF_of_ratDiv {V W : Ideal (MRingOver F ι)} {n : ℕ} {A : K → ℤ}
    {f g : MRingOver F ι} (hV : IsProjVarF V (n + 1)) (hs : IsRatSection V A f g)
    (hW : ratDiv V f g W ≠ 0) : IsProjVarF W n := by
  obtain ⟨α, β, hα, hβ, hf, hg, -⟩ := hs
  rcases mem_of_ratDiv_ne_zero hW with h | h
  · exact isProjVarF_of_mem_divSupp hV hα hf h
  · exact isProjVarF_of_mem_divSupp hV hβ hg h

/- English proof (translation)
Take `⟨α, β, hf, hg, hfV, hgV, h⟩` from `hs`. Take `⟨α', β', hf', hg', hfV', hgV', h'⟩` from `hs'`. Use `⟨α + α', β + β', isMultiHomog_mul hf hf', isMultiHomog_mul hg hg', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hm`. Break down `hV.mem_or_mem hm with h1 | h1` into its components or cases.

Conclude with `hfV h1`. Conclude with `hfV' h1`. Introduce `hm`. Break down `hV.mem_or_mem hm with h1 | h1` into its components or cases. Conclude with `hgV h1`.

Conclude with `hgV' h1`. Introduce `k`. Establish `e1` using `h k`. Establish `e2` using `h' k`. Simplify using `only [Pi.add_apply, Nat.cast_add]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem multi_isRatSection_mul {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {a b : K → ℤ}
    {f g f' g' : MRingOver F ι} (hs : IsRatSection V a f g) (hs' : IsRatSection V b f' g') :
    IsRatSection V (a + b) (f * f') (g * g') := by
  obtain ⟨α, β, hf, hg, hfV, hgV, h⟩ := hs
  obtain ⟨α', β', hf', hg', hfV', hgV', h'⟩ := hs'
  refine ⟨α + α', β + β', isMultiHomog_mul hf hf', isMultiHomog_mul hg hg', ?_, ?_, ?_⟩
  · intro hm
    rcases hV.mem_or_mem hm with h1 | h1
    · exact hfV h1
    · exact hfV' h1
  · intro hm
    rcases hV.mem_or_mem hm with h1 | h1
    · exact hgV h1
    · exact hgV' h1
  · intro k
    have e1 := h k
    have e2 := h' k
    simp only [Pi.add_apply, Nat.cast_add]
    omega

/- English proof (translation)
Simplify using `only [cycEval, mul_add, Finsupp.sum_add]`.
-/
theorem multi_cycEval_add_fun (J J' : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval (fun W => J W + J' W) D = cycEval J D + cycEval J' D := by
  simp only [cycEval, mul_add, Finsupp.sum_add]

/- English proof (translation)
Establish `hL : L = Fin.snoc (α` using `fun _ => K → ℤ) (Fin.init L) (L (Fin.last n)) := (Fin.snoc_init_self L).symm`. Use `conv_lhs => rw [hL]`. Conclude with `hI.2 V n (Fin.init L) (L (Fin.last n)) _ _ hV (isRatSection_sec hV.1 (L (Fin.last n)))`.
-/
theorem multi_eval_sec {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)}
    {n : ℕ} (hV : IsProjVarF V (n + 1)) (L : Fin (n + 1) → K → ℤ) :
    I V (n + 1) L = cycEval (fun W => I W n (Fin.init L))
      (ratDiv V (secNum F ι V (L (Fin.last n))) (secDen F ι V (L (Fin.last n)))) := by
  have hL : L = Fin.snoc (α := fun _ => K → ℤ) (Fin.init L) (L (Fin.last n)) :=
    (Fin.snoc_init_self L).symm
  conv_lhs => rw [hL]
  exact hI.2 V n (Fin.init L) (L (Fin.last n)) _ _ hV (isRatSection_sec hV.1 (L (Fin.last n)))

/- English proof (translation)
Establish `hs` using `isRatSection_sec (F := F) (ι := ι) hV.1 a`. Establish `hs'` using `isRatSection_sec (F := F) (ι := ι) hV.1 b`. Take `⟨-, -, -, -, hf, hg, -⟩` from `id hs`. Take `⟨-, -, -, -, hf', hg', -⟩` from `id hs'`. Rewrite using `[hI.2 V n L _ _ _ hV (multi_isRatSection_mul hV.1.1 hs hs'), hI.2 V n L _ _ _ hV hs, hI.2 V n L _ _ _ hV hs', ratDiv_mul hV.1.1 hf hg hf' hg', cycEval_add]`.
-/
theorem multilin_last {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)}
    {n : ℕ} (hV : IsProjVarF V (n + 1)) (L : Fin n → K → ℤ) (a b : K → ℤ) :
    I V (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L (a + b)) =
      I V (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L a) +
        I V (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b) := by
  have hs := isRatSection_sec (F := F) (ι := ι) hV.1 a
  have hs' := isRatSection_sec (F := F) (ι := ι) hV.1 b
  obtain ⟨-, -, -, -, hf, hg, -⟩ := id hs
  obtain ⟨-, -, -, -, hf', hg', -⟩ := id hs'
  rw [hI.2 V n L _ _ _ hV (multi_isRatSection_mul hV.1.1 hs hs'), hI.2 V n L _ _ _ hV hs,
    hI.2 V n L _ _ _ hV hs', ratDiv_mul hV.1.1 hf hg hf' hg', cycEval_add]

/- English proof (translation)
Establish `hsw : ∀ (h t : MRingOver F ι) (β γ : K → ℕ), IsMultiHomog h β → IsMultiHomog t γ → h ∉ V → t ∉ V → (∀ W ∈ divSupp V h, t ∉ W) → cycEval (fun W => cycEval J (ratDiv W t 1)) (ratDiv V h 1) = cycEval (fun W => cycEval J (ratDiv W h 1)) (ratDiv V t 1)`. Introduce `h t β γ hh ht hhV htV hht`. Rewrite using `[← cycEval_sum_smul, ← cycEval_sum_smul, swap_cycle (n := n) hV hh ht hhV htV hht]`. Establish `fe : (fun W => cycEval J (ratDiv W t₁ t₂)) = fun W => cycEval J (ratDiv W t₁ 1) - cycEval J (ratDiv W t₂ 1)`. Use function extensionality and compare the values at `fun W => by rw [ratDiv_eq_sub W t₁ t₂, cycEval_sub]`.

Establish `fe' : (fun W => cycEval J (ratDiv W f g)) = fun W => cycEval J (ratDiv W f 1) - cycEval J (ratDiv W g 1)`. Use function extensionality and compare the values at `fun W => by rw [ratDiv_eq_sub W f g, cycEval_sub]`. Rewrite using `[fe, fe', ratDiv_eq_sub V f g, ratDiv_eq_sub V t₁ t₂]`. Simplify using `only [cycEval_sub_fun, cycEval_sub]`. Rewrite using `[hsw f t₁ α _ hf ht₁ hfV ht₁V hft₁, hsw f t₂ α _ hf ht₂ hfV ht₂V hft₂, hsw g t₁ β _ hg ht₁ hgV ht₁V hgt₁, hsw g t₂ β _ hg ht₂ hgV ht₂V hgt₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem multi_swap4 {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V (n + 2))
    (J : Ideal (MRingOver F ι) → ℤ) {f g t₁ t₂ : MRingOver F ι} {α β γ δ : K → ℕ}
    (hf : IsMultiHomog f α) (hg : IsMultiHomog g β) (ht₁ : IsMultiHomog t₁ γ)
    (ht₂ : IsMultiHomog t₂ δ) (hfV : f ∉ V) (hgV : g ∉ V) (ht₁V : t₁ ∉ V) (ht₂V : t₂ ∉ V)
    (hft₁ : ∀ W ∈ divSupp V f, t₁ ∉ W) (hft₂ : ∀ W ∈ divSupp V f, t₂ ∉ W)
    (hgt₁ : ∀ W ∈ divSupp V g, t₁ ∉ W) (hgt₂ : ∀ W ∈ divSupp V g, t₂ ∉ W) :
    cycEval (fun W => cycEval J (ratDiv W t₁ t₂)) (ratDiv V f g) =
      cycEval (fun W => cycEval J (ratDiv W f g)) (ratDiv V t₁ t₂) := by
  have hsw : ∀ (h t : MRingOver F ι) (β γ : K → ℕ), IsMultiHomog h β → IsMultiHomog t γ →
      h ∉ V → t ∉ V → (∀ W ∈ divSupp V h, t ∉ W) →
      cycEval (fun W => cycEval J (ratDiv W t 1)) (ratDiv V h 1) =
        cycEval (fun W => cycEval J (ratDiv W h 1)) (ratDiv V t 1) := by
    intro h t β γ hh ht hhV htV hht
    rw [← cycEval_sum_smul, ← cycEval_sum_smul, swap_cycle (n := n) hV hh ht hhV htV hht]
  have fe : (fun W => cycEval J (ratDiv W t₁ t₂)) =
      fun W => cycEval J (ratDiv W t₁ 1) - cycEval J (ratDiv W t₂ 1) :=
    funext fun W => by rw [ratDiv_eq_sub W t₁ t₂, cycEval_sub]
  have fe' : (fun W => cycEval J (ratDiv W f g)) =
      fun W => cycEval J (ratDiv W f 1) - cycEval J (ratDiv W g 1) :=
    funext fun W => by rw [ratDiv_eq_sub W f g, cycEval_sub]
  rw [fe, fe', ratDiv_eq_sub V f g, ratDiv_eq_sub V t₁ t₂]
  simp only [cycEval_sub_fun, cycEval_sub]
  rw [hsw f t₁ α _ hf ht₁ hfV ht₁V hft₁, hsw f t₂ α _ hf ht₂ hfV ht₂V hft₂,
    hsw g t₁ β _ hg ht₁ hgV ht₁V hgt₁, hsw g t₂ β _ hg ht₂ hgV ht₂V hgt₂]
  ring

/- English proof (translation)
Use `set J : Ideal (MRingOver F ι) → ℤ := fun W => I W n L with hJ`. Establish `hs` using `isRatSection_sec (F := F) (ι := ι) hV.1 b`. Use `set s₁ := secNum F ι V b with hs₁`. Use `set s₂ := secDen F ι V b with hs₂`. Take `⟨α, β, hα, hβ, hs₁V, hs₂V, hαβ⟩` from `id hs`.

Use `set S : Set (Ideal (MRingOver F ι)) := divSupp V s₁ ∪ divSupp V s₂ ∪ {V} with hSdef`. Establish `hSf : S.Finite` using `((divSupp_finite V s₁).union (divSupp_finite V s₂)).union (Set.finite_singleton V)`. Establish `hS : ∀ W ∈ S, IsMultiProjPrime W`. Introduce and unpack `W ((hW | hW) | hW)`. Conclude with `(isProjVarF_of_mem_divSupp hV hα hs₁V hW).1`.

Conclude with `(isProjVarF_of_mem_divSupp hV hβ hs₂V hW).1`. Rewrite using `[Set.mem_singleton_iff.mp hW]`. Conclude with `hV.1`. Take `⟨d₀, hd₀⟩` from `exists_form_avoid S hSf hS`. Take `⟨t₁, ht₁, ht₁S⟩` from `hd₀ (d₀ + fun k => (a k).toNat) (fun k => by simp)`.

Take `⟨t₂, ht₂, ht₂S⟩` from `hd₀ (d₀ + fun k => (-a k).toNat) (fun k => by simp)`. Establish `hVS : V ∈ S` using `Or.inr rfl`. Establish `ht₁V` using `ht₁S V hVS`. Establish `ht₂V` using `ht₂S V hVS`. Establish `hsecW : ∀ W ∈ S, IsRatSection W a t₁ t₂` using `fun W hW => ⟨_, _, ht₁, ht₂, ht₁S W hW, ht₂S W hW, fun k => by`.

Use `Int.toNat_sub_toNat_neg (a k)` as an intermediate fact. Simplify using `only [Pi.add_apply, Nat.cast_add]`. Use the proof step `omega⟩`. Establish `hs₁t₁ : ∀ W ∈ divSupp V s₁, t₁ ∉ W` using `fun W hW => ht₁S W (Or.inl (Or.inl hW))`. Establish `hs₁t₂ : ∀ W ∈ divSupp V s₁, t₂ ∉ W` using `fun W hW => ht₂S W (Or.inl (Or.inl hW))`.

Establish `hs₂t₁ : ∀ W ∈ divSupp V s₂, t₁ ∉ W` using `fun W hW => ht₁S W (Or.inl (Or.inr hW))`. Establish `hs₂t₂ : ∀ W ∈ divSupp V s₂, t₂ ∉ W` using `fun W hW => ht₂S W (Or.inl (Or.inr hW))`. Establish `h1 : I V (n + 2) (Fin.snoc (α` using `fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L a) b) = cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L a)) (ratDiv V s₁ s₂) := hI.2 V (n + 1) _ b _ _ hV hs`. Establish `h2 : I V (n + 2) (Fin.snoc (α` using `fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L b) a) = cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (ratDiv V t₁ t₂) := hI.2 V (n + 1) _ a _ _ hV (hsecW V hVS)`. Establish `h3 : cycEval (fun W => I W (n + 1) (Fin.snoc (α` using `fun _ => K → ℤ) L a)) (ratDiv V s₁ s₂) = cycEval (fun W => cycEval J (ratDiv W t₁ t₂)) (ratDiv V s₁ s₂) := by`.

Apply `cycEval_congr` to reduce the goal to its premises. Introduce `W hW`. Establish `hWS : W ∈ S`. Break down `mem_of_ratDiv_ne_zero hW with h | h` into its components or cases. Conclude with `Or.inl (Or.inl h)`.

Conclude with `Or.inl (Or.inr h)`. Conclude with `hI.2 W n L a t₁ t₂ (multi_isProjVarF_of_ratDiv hV hs hW) (hsecW W hWS)`. Establish `h4 : cycEval (fun W => I W (n + 1) (Fin.snoc (α` using `fun _ => K → ℤ) L b)) (ratDiv V t₁ t₂) = cycEval (fun W => cycEval J (ratDiv W s₁ s₂)) (ratDiv V t₁ t₂) := by`. Apply `cycEval_congr` to reduce the goal to its premises. Introduce `W hW`.

Establish `hWv` using `multi_isProjVarF_of_ratDiv hV (hsecW V hVS) hW`. Establish `hsW : IsRatSection W b s₁ s₂`. Use `⟨α, β, hα, hβ, ?_, ?_, hαβ⟩` and prove the remaining obligations. Break down `mem_of_ratDiv_ne_zero hW with h | h` into its components or cases. Conclude with `not_mem_of_mem_divSupp_swap (n := n + 1) hV hα ht₁ hs₁V ht₁V hs₁t₁ h`.

Conclude with `not_mem_of_mem_divSupp_swap (n := n + 1) hV hα ht₂ hs₁V ht₂V hs₁t₂ h`. Break down `mem_of_ratDiv_ne_zero hW with h | h` into its components or cases. Conclude with `not_mem_of_mem_divSupp_swap (n := n + 1) hV hβ ht₁ hs₂V ht₁V hs₂t₁ h`. Conclude with `not_mem_of_mem_divSupp_swap (n := n + 1) hV hβ ht₂ hs₂V ht₂V hs₂t₂ h`. Conclude with `hI.2 W n L b s₁ s₂ hWv hsW`.

Rewrite using `[h1, h2, h3, h4]`. Conclude with `multi_swap4 hV J hα hβ ht₁ ht₂ hs₁V hs₂V ht₁V ht₂V hs₁t₁ hs₁t₂ hs₂t₁ hs₂t₂`.
-/
theorem symm_last_two {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)}
    {n : ℕ} (hV : IsProjVarF V (n + 2)) (L : Fin n → K → ℤ) (a b : K → ℤ) :
    I V (n + 2) (Fin.snoc (α := fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L a) b) =
      I V (n + 2) (Fin.snoc (α := fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L b) a) := by
  classical
  set J : Ideal (MRingOver F ι) → ℤ := fun W => I W n L with hJ
  have hs := isRatSection_sec (F := F) (ι := ι) hV.1 b
  set s₁ := secNum F ι V b with hs₁
  set s₂ := secDen F ι V b with hs₂
  obtain ⟨α, β, hα, hβ, hs₁V, hs₂V, hαβ⟩ := id hs
  set S : Set (Ideal (MRingOver F ι)) := divSupp V s₁ ∪ divSupp V s₂ ∪ {V} with hSdef
  have hSf : S.Finite :=
    ((divSupp_finite V s₁).union (divSupp_finite V s₂)).union (Set.finite_singleton V)
  have hS : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W ((hW | hW) | hW)
    · exact (isProjVarF_of_mem_divSupp hV hα hs₁V hW).1
    · exact (isProjVarF_of_mem_divSupp hV hβ hs₂V hW).1
    · rw [Set.mem_singleton_iff.mp hW]
      exact hV.1
  obtain ⟨d₀, hd₀⟩ := exists_form_avoid S hSf hS
  obtain ⟨t₁, ht₁, ht₁S⟩ := hd₀ (d₀ + fun k => (a k).toNat) (fun k => by simp)
  obtain ⟨t₂, ht₂, ht₂S⟩ := hd₀ (d₀ + fun k => (-a k).toNat) (fun k => by simp)
  have hVS : V ∈ S := Or.inr rfl
  have ht₁V := ht₁S V hVS
  have ht₂V := ht₂S V hVS
  have hsecW : ∀ W ∈ S, IsRatSection W a t₁ t₂ := fun W hW =>
    ⟨_, _, ht₁, ht₂, ht₁S W hW, ht₂S W hW, fun k => by
      have := Int.toNat_sub_toNat_neg (a k)
      simp only [Pi.add_apply, Nat.cast_add]
      omega⟩
  have hs₁t₁ : ∀ W ∈ divSupp V s₁, t₁ ∉ W := fun W hW => ht₁S W (Or.inl (Or.inl hW))
  have hs₁t₂ : ∀ W ∈ divSupp V s₁, t₂ ∉ W := fun W hW => ht₂S W (Or.inl (Or.inl hW))
  have hs₂t₁ : ∀ W ∈ divSupp V s₂, t₁ ∉ W := fun W hW => ht₁S W (Or.inl (Or.inr hW))
  have hs₂t₂ : ∀ W ∈ divSupp V s₂, t₂ ∉ W := fun W hW => ht₂S W (Or.inl (Or.inr hW))
  have h1 : I V (n + 2) (Fin.snoc (α := fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L a) b) =
      cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L a)) (ratDiv V s₁ s₂) :=
    hI.2 V (n + 1) _ b _ _ hV hs
  have h2 : I V (n + 2) (Fin.snoc (α := fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) L b) a) =
      cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (ratDiv V t₁ t₂) :=
    hI.2 V (n + 1) _ a _ _ hV (hsecW V hVS)
  have h3 : cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L a)) (ratDiv V s₁ s₂) =
      cycEval (fun W => cycEval J (ratDiv W t₁ t₂)) (ratDiv V s₁ s₂) := by
    apply cycEval_congr
    intro W hW
    have hWS : W ∈ S := by
      rcases mem_of_ratDiv_ne_zero hW with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
    exact hI.2 W n L a t₁ t₂ (multi_isProjVarF_of_ratDiv hV hs hW) (hsecW W hWS)
  have h4 : cycEval (fun W => I W (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (ratDiv V t₁ t₂) =
      cycEval (fun W => cycEval J (ratDiv W s₁ s₂)) (ratDiv V t₁ t₂) := by
    apply cycEval_congr
    intro W hW
    have hWv := multi_isProjVarF_of_ratDiv hV (hsecW V hVS) hW
    have hsW : IsRatSection W b s₁ s₂ := by
      refine ⟨α, β, hα, hβ, ?_, ?_, hαβ⟩
      · rcases mem_of_ratDiv_ne_zero hW with h | h
        · exact not_mem_of_mem_divSupp_swap (n := n + 1) hV hα ht₁ hs₁V ht₁V hs₁t₁ h
        · exact not_mem_of_mem_divSupp_swap (n := n + 1) hV hα ht₂ hs₁V ht₂V hs₁t₂ h
      · rcases mem_of_ratDiv_ne_zero hW with h | h
        · exact not_mem_of_mem_divSupp_swap (n := n + 1) hV hβ ht₁ hs₂V ht₁V hs₂t₁ h
        · exact not_mem_of_mem_divSupp_swap (n := n + 1) hV hβ ht₂ hs₂V ht₂V hs₂t₂ h
    exact hI.2 W n L b s₁ s₂ hWv hsW
  rw [h1, h2, h3, h4]
  exact multi_swap4 hV J hα hβ ht₁ ht₂ hs₁V hs₂V ht₁V ht₂V hs₁t₁ hs₁t₂ hs₂t₁ hs₂t₂

/- English proof (translation)
Establish `hL : L = Fin.snoc (α` using `fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) (Fin.init (Fin.init L)) (L (Fin.last m).castSucc)) (L (Fin.last (m + 1))) := by`. Use function extensionality and compare the values at `t`. Use `Fin.lastCases ?_ (fun t => ?_) t` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `Fin.lastCases ?_ (fun t => ?_) t` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `[Fin.init]`. Establish `hL' : L ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) = Fin.snoc (α` using `fun _ => K → ℤ) (Fin.snoc (α := fun _ => K → ℤ) (Fin.init (Fin.init L)) (L (Fin.last (m + 1)))) (L (Fin.last m).castSucc) := by`. Use function extensionality and compare the values at `t`. Use `Fin.lastCases ?_ (fun t => ?_) t` and prove the remaining obligations.

Simplify using `[Equiv.swap_apply_right]`. Use `Fin.lastCases ?_ (fun t => ?_) t` and prove the remaining obligations. Simplify using `[Equiv.swap_apply_left]`. Establish `h1 : t.castSucc.castSucc ≠ (Fin.last m).castSucc`. Introduce `h`.

Conclude with `(Fin.castSucc_lt_last t).ne (Fin.castSucc_injective _ h)`. Establish `h2 : t.castSucc.castSucc ≠ Fin.last (m + 1)` using `(Fin.castSucc_lt_last _).ne`. Simplify using `[Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.init]`. Rewrite using `[hL', symm_last_two hI hV, ← hL]`.
-/
theorem multi_swap_last_two {I : IFamily F ι} (hI : IsFieldIntersection I)
    {V : Ideal (MRingOver F ι)} {m : ℕ} (hV : IsProjVarF V (m + 1 + 1))
    (L : Fin (m + 1 + 1) → K → ℤ) :
    I V (m + 1 + 1) (L ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) =
      I V (m + 1 + 1) L := by
  have hL : L = Fin.snoc (α := fun _ => K → ℤ)
      (Fin.snoc (α := fun _ => K → ℤ) (Fin.init (Fin.init L)) (L (Fin.last m).castSucc)) (L (Fin.last (m + 1))) := by
    funext t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp
    · refine Fin.lastCases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.init]
  have hL' : L ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) = Fin.snoc (α := fun _ => K → ℤ)
      (Fin.snoc (α := fun _ => K → ℤ) (Fin.init (Fin.init L)) (L (Fin.last (m + 1)))) (L (Fin.last m).castSucc) := by
    funext t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp [Equiv.swap_apply_right]
    · refine Fin.lastCases ?_ (fun t => ?_) t
      · simp [Equiv.swap_apply_left]
      · have h1 : t.castSucc.castSucc ≠ (Fin.last m).castSucc := by
          intro h; exact (Fin.castSucc_lt_last t).ne (Fin.castSucc_injective _ h)
        have h2 : t.castSucc.castSucc ≠ Fin.last (m + 1) := (Fin.castSucc_lt_last _).ne
        simp [Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.init]
  rw [hL', symm_last_two hI hV, ← hL]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V L σ _`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `i.elim0`. Consider the case `succ n ih`. Establish `hcs : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x y : Fin n), IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x.castSucc y.castSucc) = I V (n + 1) L`. Introduce `V L x y hV`. Rewrite using `[multi_eval_sec hI hV, multi_eval_sec hI hV (L := L)]`.

Establish `e1 : (L ∘ Equiv.swap x.castSucc y.castSucc) (Fin.last n) = L (Fin.last n)`. Simplify using `only [Function.comp_apply]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last x).symm (Fin.castSucc_ne_last y).symm]`. Establish `e2 : Fin.init (L ∘ Equiv.swap x.castSucc y.castSucc) = Fin.init L ∘ Equiv.swap x y`. Use function extensionality and compare the values at `i`.

Simplify using `only [Fin.init, Function.comp_apply]`. Rewrite using `[(Fin.castSucc_injective n).swap_apply]`. Rewrite using `[e1, e2]`. Apply `cycEval_congr` to reduce the goal to its premises. Introduce `W hW`.

Conclude with `ih W _ _ (multi_isProjVarF_of_ratDiv hV (isRatSection_sec hV.1 _) hW)`. Establish `hlast : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x : Fin n), IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x.castSucc (Fin.last n)) = I V (n + 1) L`. Introduce `V L x hV`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `Nat.exists_eq_succ_of_ne_zero (Fin.pos x).ne'`. Distinguish the cases in `hx : x = Fin.last m`.

Substitute `hx` using the available equality. Conclude with `multi_swap_last_two hI hV L`. Establish `hxk : x.castSucc ≠ (Fin.last m).castSucc` using `fun h => hx (Fin.castSucc_injective _ h)`. Establish `hxl : x.castSucc ≠ Fin.last (m + 1)` using `Fin.castSucc_ne_last _`. Establish `e : Equiv.swap x.castSucc (Fin.last (m + 1)) = Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) * Equiv.swap x.castSucc (Fin.last m).castSucc * Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))`.

Rewrite using `[Equiv.swap_mul_swap_mul_swap hxk hxl, Equiv.swap_comm]`. Rewrite using `[e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul]`. Express the relevant statement in the definitionally equal form `I V (m + 1 + 1) (((L ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) ∘ Equiv.swap x.castSucc (Fin.last m).castSucc) ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) = _`. Rewrite using `[multi_swap_last_two hI hV, hcs V _ x (Fin.last m) hV, multi_swap_last_two hI hV]`. Establish `hsw : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x y : Fin (n + 1)), IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x y) = I V (n + 1) L`.

Introduce `V L x y hV`. Distinguish the cases in `hx : x = Fin.last n`. Distinguish the cases in `hy : y = Fin.last n`. Substitute `hx` using the available equality. Substitute `hy` using the available equality.

Rewrite using `[Equiv.swap_self, Equiv.coe_refl, Function.comp_id]`. Take `⟨y', rfl⟩` from `Fin.exists_castSucc_eq.mpr hy`. Substitute `hx` using the available equality. Rewrite using `[Equiv.swap_comm]`. Conclude with `hlast V L y' hV`.

Take `⟨x', rfl⟩` from `Fin.exists_castSucc_eq.mpr hx`. Distinguish the cases in `hy : y = Fin.last n`. Substitute `hy` using the available equality. Conclude with `hlast V L x' hV`. Take `⟨y', rfl⟩` from `Fin.exists_castSucc_eq.mpr hy`.

Conclude with `hcs V L x' y' hV`. Introduce `V L σ hV`. Use `revert L`. Use `Equiv.Perm.swap_induction_on (motive := fun σ => ∀ L : Fin (n + 1) → K → ℤ, I V (n + 1) (L ∘ σ) = I V (n + 1) L) σ (fun L => by simp) (fun f x y _ hf L => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hsw V L x y hV]`.
-/
theorem intersection_symmetric {I : IFamily F ι} (hI : IsFieldIntersection I) (n : ℕ) :
    ∀ (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsProjVarF V n → I V n (L ∘ σ) = I V n L := by
  induction n with
  | zero =>
    intro V L σ _
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    have hcs : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x y : Fin n),
        IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x.castSucc y.castSucc) = I V (n + 1) L := by
      intro V L x y hV
      rw [multi_eval_sec hI hV, multi_eval_sec hI hV (L := L)]
      have e1 : (L ∘ Equiv.swap x.castSucc y.castSucc) (Fin.last n) = L (Fin.last n) := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last x).symm (Fin.castSucc_ne_last y).symm]
      have e2 : Fin.init (L ∘ Equiv.swap x.castSucc y.castSucc) = Fin.init L ∘ Equiv.swap x y := by
        funext i
        simp only [Fin.init, Function.comp_apply]
        rw [(Fin.castSucc_injective n).swap_apply]
      rw [e1, e2]
      apply cycEval_congr
      intro W hW
      exact ih W _ _ (multi_isProjVarF_of_ratDiv hV (isRatSection_sec hV.1 _) hW)
    have hlast : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x : Fin n),
        IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x.castSucc (Fin.last n)) =
          I V (n + 1) L := by
      intro V L x hV
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos x).ne'
      by_cases hx : x = Fin.last m
      · subst hx
        exact multi_swap_last_two hI hV L
      · have hxk : x.castSucc ≠ (Fin.last m).castSucc := fun h => hx (Fin.castSucc_injective _ h)
        have hxl : x.castSucc ≠ Fin.last (m + 1) := Fin.castSucc_ne_last _
        have e : Equiv.swap x.castSucc (Fin.last (m + 1)) =
            Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) *
              Equiv.swap x.castSucc (Fin.last m).castSucc *
                Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) := by
          rw [Equiv.swap_mul_swap_mul_swap hxk hxl, Equiv.swap_comm]
        rw [e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul]
        change I V (m + 1 + 1) (((L ∘ Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) ∘
          Equiv.swap x.castSucc (Fin.last m).castSucc) ∘
            Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) = _
        rw [multi_swap_last_two hI hV, hcs V _ x (Fin.last m) hV, multi_swap_last_two hI hV]
    have hsw : ∀ (V : Ideal (MRingOver F ι)) (L : Fin (n + 1) → K → ℤ) (x y : Fin (n + 1)),
        IsProjVarF V (n + 1) → I V (n + 1) (L ∘ Equiv.swap x y) = I V (n + 1) L := by
      intro V L x y hV
      by_cases hx : x = Fin.last n
      · by_cases hy : y = Fin.last n
        · subst hx; subst hy
          rw [Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
        · obtain ⟨y', rfl⟩ := Fin.exists_castSucc_eq.mpr hy
          subst hx
          rw [Equiv.swap_comm]
          exact hlast V L y' hV
      · obtain ⟨x', rfl⟩ := Fin.exists_castSucc_eq.mpr hx
        by_cases hy : y = Fin.last n
        · subst hy
          exact hlast V L x' hV
        · obtain ⟨y', rfl⟩ := Fin.exists_castSucc_eq.mpr hy
          exact hcs V L x' y' hV
    intro V L σ hV
    revert L
    refine Equiv.Perm.swap_induction_on
      (motive := fun σ => ∀ L : Fin (n + 1) → K → ℤ, I V (n + 1) (L ∘ σ) = I V (n + 1) L) σ
      (fun L => by simp) (fun f x y _ hf L => ?_)
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hsw V L x y hV]

/- English proof (translation)
Introduce `V L j a b hV`. Consider the cases of `n with`. Consider the case `zero => exact j.elim0`. Consider the case `succ m => set σ := Equiv.swap j (Fin.last m) with hσ`. Establish `key : ∀ c : K → ℤ, I V (m + 1) (Function.update L j c) = I V (m + 1) (Fin.snoc (α` using `fun _ => K → ℤ) (Fin.init (L ∘ σ)) c) := by`.

Introduce `c`. Rewrite using `[← intersection_symmetric hI (m + 1) V (Function.update L j c) σ hV]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun i' => ?_) i` and prove the remaining obligations.

Simplify using `[hσ, Fin.snoc_last]`. Establish `h2 : σ (Fin.castSucc i') ≠ j`. Introduce `h`. Apply `(Fin.castSucc_lt_last i').ne` to reduce the goal to its premises. Establish `h3` using `congrArg σ h`.

Rewrite `h3` using `[hσ, Equiv.swap_apply_self, Equiv.swap_apply_left]`. Conclude with `h3`. Simplify using `only [Function.comp, Fin.snoc_castSucc, Fin.init]`. Rewrite using `[Function.update_of_ne h2]`. Rewrite using `[key, key, key, multilin_last hI hV]`.
-/
theorem intersection_multilinear {I : IFamily F ι} (hI : IsFieldIntersection I) (n : ℕ) :
    ∀ (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ),
      IsProjVarF V n → I V n (Function.update L j (a + b)) =
        I V n (Function.update L j a) + I V n (Function.update L j b) := by
  intro V L j a b hV
  cases n with
  | zero => exact j.elim0
  | succ m =>
    set σ := Equiv.swap j (Fin.last m) with hσ
    have key : ∀ c : K → ℤ, I V (m + 1) (Function.update L j c) =
        I V (m + 1) (Fin.snoc (α := fun _ => K → ℤ) (Fin.init (L ∘ σ)) c) := by
      intro c
      rw [← intersection_symmetric hI (m + 1) V (Function.update L j c) σ hV]
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [hσ, Fin.snoc_last]
      · have h2 : σ (Fin.castSucc i') ≠ j := by
          intro h
          apply (Fin.castSucc_lt_last i').ne
          have h3 := congrArg σ h
          rw [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at h3
          exact h3
        simp only [Function.comp, Fin.snoc_castSucc, Fin.init]
        rw [Function.update_of_ne h2]
    rw [key, key, key, multilin_last hI hV]

/- English proof (translation)
Introduce `I hI V n L σ hV`. Conclude with `intersection_symmetric hI n V L σ hV`.
-/
theorem symm_thm (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  intro I hI V n L σ hV
  exact intersection_symmetric hI n V L σ hV

/- English proof (translation)
Introduce `I hI V n L j a b hV`. Conclude with `intersection_multilinear hI n V L j a b hV`.
-/
theorem multilin_thm (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MultilinStatement F ι := by
  intro I hI V n L j a b hV
  exact intersection_multilinear hI n V L j a b hV

end ReciprocityTheory.ChartRestriction.G.AI.I1
