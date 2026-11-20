import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanLevel

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

structure WData (G P : Type) [Group G] [Group P] where
  ι : G →* P
  ρ : P →* G
  ℓ : Additive P →+ ℤ
  t : P
  ρι : ∀ g, ρ (ι g) = g
  ρt : ρ t = 1
  ℓι : ∀ g, ℓ (Additive.ofMul (ι g)) = 0
  ℓt : ℓ (Additive.ofMul t) = 1
  tc : ∀ z, t * z = z * t
  dec : ∀ p, p = ι (ρ p) * t ^ (ℓ (Additive.ofMul p))

variable {G P : Type} [Group G] [Group P] (W : WData G P)

def WData.pr (z : P) : P := W.ι (W.ρ z)

def WData.ps (z : P) : P := W.t⁻¹ * W.ι (W.ρ z)

/- English proof (translation)
The claim follows from `(W.tc g).symm`.
-/
theorem WData.comm_range (g : P) (_hg : g ∈ Set.range W.ι) : g * W.t = W.t * g := (W.tc g).symm

/- English proof (translation)
Take `⟨g', rfl⟩` from `hg`. Simplify using `[WData.pr, W.ρι]`.
-/
theorem WData.pr_mul (g : P) (hg : g ∈ Set.range W.ι) (z : P) : W.pr (g * z) = g * W.pr z := by
  obtain ⟨g', rfl⟩ := hg
  simp [WData.pr, W.ρι]

/- English proof (translation)
Take `⟨g', rfl⟩` from `hg`. Establish `h1 : W.t⁻¹ * W.ι g' = W.ι g' * W.t⁻¹`. Use `W.tc (W.ι g')` as an intermediate fact. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, this, mul_inv_cancel_right]`. Simplify using `only [WData.ps, map_mul, W.ρι]`.

Rewrite using `[← mul_assoc, h1, mul_assoc]`.
-/
theorem WData.ps_mul (g : P) (hg : g ∈ Set.range W.ι) (z : P) : W.ps (g * z) = g * W.ps z := by
  obtain ⟨g', rfl⟩ := hg
  have h1 : W.t⁻¹ * W.ι g' = W.ι g' * W.t⁻¹ := by
    have := W.tc (W.ι g')
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, this, mul_inv_cancel_right]
  simp only [WData.ps, map_mul, W.ρι]
  rw [← mul_assoc, h1, mul_assoc]

/- English proof (translation)
Establish `hk : ∀ k : ℤ, ∀ y, F (fun i => W.t ^ k * y i) = F y`. Introduce `k`. Proceed by induction on `k using Int.induction_on with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `y`. Rewrite using `[← ih y, ← ht (fun i => W.t ^ (k : ℤ) * y i)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← mul_assoc, ← zpow_one_add, add_comm]`. Consider the case `pred k ih`. Introduce `y`. Rewrite using `[← ih y, ← ht (fun i => W.t ^ (-(k : ℤ) - 1) * y i)]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, ← zpow_one_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Introduce `p _ y`.

Establish `: (fun i => p * y i) = fun i => W.ι (W.ρ p) * (W.t ^ (W.ℓ (Additive.ofMul p)) * y i)`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, ← W.dec p]`. Rewrite using `[this, hS _ ⟨_, rfl⟩, hk]`.
-/
theorem WData.inv_univ {n : ℕ} (F : (Fin n → P) → ℝ) (hS : InvS (Set.range W.ι) F)
    (ht : ∀ y, F (fun i => W.t * y i) = F y) : InvS Set.univ F := by
  have hk : ∀ k : ℤ, ∀ y, F (fun i => W.t ^ k * y i) = F y := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (k : ℤ) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add, add_comm]
    | pred k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (-(k : ℤ) - 1) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add]; congr 2; ring
  intro p _ y
  have : (fun i => p * y i) = fun i => W.ι (W.ρ p) * (W.t ^ (W.ℓ (Additive.ofMul p)) * y i) := by
    funext i; rw [← mul_assoc, ← W.dec p]
  rw [this, hS _ ⟨_, rfl⟩, hk]

/- English proof (translation)
Use `choose g hg using hz`. Establish `: z = fun i => W.ι (g i)` using `by funext i; exact (hg i).symm`. Rewrite using `[this, hF]`.
-/
theorem WData.vanish_range {n : ℕ} (F : (Fin n → P) → ℝ) (hF : ∀ g : Fin n → G, F (fun i => W.ι (g i)) = 0)
    (z : Fin n → P) (hz : ∀ i, z i ∈ Set.range W.ι) : F z = 0 := by
  choose g hg using hz
  have : z = fun i => W.ι (g i) := by funext i; exact (hg i).symm
  rw [this, hF]

/- English proof (translation)
Simplify using `[dc, Fin.sum_univ_succ]`. Establish `h1 : (fun j : Fin 1 => (Fin.cons a y : Fin 2 → Y) (Fin.succAbove 1 j)) = fun _ => a`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dc_one {Y : Type} (F : (Fin 1 → Y) → ℝ) (a : Y) (y : Fin 1 → Y) :
    dc F (Fin.cons a y) = F y - F (fun _ => a) := by
  simp [dc, Fin.sum_univ_succ]
  have h1 : (fun j : Fin 1 => (Fin.cons a y : Fin 2 → Y) (Fin.succAbove 1 j)) = fun _ => a := by
    funext j; fin_cases j; rfl
  rw [h1]
  ring

/- English proof (translation)
Use `set S := Set.range W.ι with hSdef`. Establish `hcS : InvS S c` using `fun g _ y => hc g trivial y`. Establish `hprS : ∀ z ∈ S, W.pr z ∈ S` using `fun z _ => ⟨_, rfl⟩`. Use `set x := prism W.pr c with hxdef`. Establish `hxS : InvS S x` using `prism_inv W.pr S W.pr_mul c hcS`.

Establish `hdx : dc x = -c`. Use function extensionality and compare the values at `y`. Establish `h` using `prism_dc W.pr m c y`. Rewrite `h` using `[hdc, prism_zero]`. Establish `h0 : c (fun i => W.pr (y i)) = 0` using `hres (fun i => W.ρ (y i))`.

Simplify using `only [Pi.zero_apply, add_zero, h0, zero_sub] at h`. Simplify using `using h`. Establish `hx0 : ∀ g : Fin (m + 1) → G, x (fun i => W.ι (g i)) = 0` using `fun g => prism_eq_zero_of_set W.pr S hprS c _ (W.vanish_range c hres) (fun i => ⟨_, rfl⟩)`. Establish `hxt : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) = 0`. Introduce `g`.

Rewrite using `[hxdef, prism_mul]`. Establish `e1 : (fun z => W.t⁻¹ * W.pr (W.t * z)) = W.ps`. Use function extensionality and compare the values at `z`. Simplify using `[WData.pr, WData.ps, W.ρt]`. Establish `e2 : (fun z : Fin (m + 2) → P => c (fun i => W.t * z i)) = c`.

Use function extensionality and compare the values at `z`. Conclude with `hc _ trivial z`. Rewrite using `[e1, e2]`. Conclude with `hsl g`. Establish `hv0 : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) - x (fun i => W.ι (g i)) = 0`.

Introduce `g`. Rewrite using `[hxt, hx0, sub_zero]`. Establish `hdv : dc ((fun y => x (fun i => W.t * y i)) - x) = 0`. Rewrite using `[dc_sub]`. Use function extensionality and compare the values at `z`.

Simplify using `only [Pi.sub_apply, Pi.zero_apply]`. Rewrite using `[dc_comp x (fun p => W.t * p) z, hdx]`. Simplify using `only [Pi.neg_apply]`. Rewrite using `[hc _ trivial z]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hvS : InvS S ((fun y => x (fun i => W.t * y i)) - x)`. Introduce `g hg y`. Simplify using `only [Pi.sub_apply]`. Establish `: (fun i => W.t * (g * y i)) = fun i => g * (W.t * y i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[← mul_assoc, ← mul_assoc, W.comm_range g hg]`. Rewrite using `[this, hxS g hg, hxS g hg]`. Consider the cases of `m with`. Consider the case `zero`. Establish `hvz : ∀ y : Fin 1 → P, x (fun i => W.t * y i) = x y`.

Introduce `y`. Establish `h` using `congrFun hdv (Fin.cons (W.ι 1) y)`. Rewrite `h` using `[dc_one]`. Establish `h1` using `hv0 (fun _ => 1)`. Simplify using `only [Pi.sub_apply, Pi.zero_apply] at h h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨-x, ?_, ?_⟩` and prove the remaining obligations. Establish `hx` using `W.inv_univ x hxS hvz`. Introduce `g hg y`. Simplify using `only [Pi.neg_apply]`.

Rewrite using `[hx g hg y]`. Rewrite using `[dc_neg, hdx, neg_neg]`. Consider the case `succ m' => set v := (fun y => x (fun i => W.t * y i)) - x with hvdef set w := -prism W.pr v with hwdef`. Establish `hdw : dc w = v`. Use function extensionality and compare the values at `y`.

Establish `h` using `prism_dc W.pr m' v y`. Rewrite `h` using `[hdv, prism_zero]`. Establish `h0 : v (fun i => W.pr (y i)) = 0` using `hv0 (fun i => W.ρ (y i))`. Simplify using `only [Pi.zero_apply, add_zero, h0, zero_sub] at h`. Rewrite using `[hwdef, dc_neg, Pi.neg_apply, h, neg_neg]`.

Establish `hwS : InvS S w`. Introduce `g hg y`. Simplify using `only [hwdef, Pi.neg_apply]`. Rewrite using `[prism_inv W.pr S W.pr_mul v hvS g hg y]`. Use `set lev : P → ℤ := fun z => W.ℓ (Additive.ofMul z) with hlevdef`.

Establish `hlev : ∀ z, lev (W.t * z) = lev z + 1`. Introduce `z`. Simplify using `only [hlevdef, ofMul_mul, map_add, W.ℓt]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlevS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z`.

Introduce and unpack `g ⟨g', rfl⟩ z`. Simplify using `only [hlevdef, ofMul_mul, map_add, W.ℓι, zero_add]`. Use `set w' := levSum W.t lev w with hw'def`. Establish `hw'S : InvS S w'` using `levSum_inv W.t lev S hlevS W.comm_range w hwS`. Establish `hw'w : (fun y => w' (fun i => W.t * y i)) - w' = w`.

Use function extensionality and compare the values at `y`. Conclude with `levSum_spec W.t lev hlev w y`. Use `set e0 := x - dc w' with he0def`. Establish `he0S : InvS S e0`. Introduce `g hg y`.

Simplify using `only [he0def, Pi.sub_apply]`. Rewrite using `[hxS g hg y, dc_inv S w' hw'S g hg y]`. Establish `he0t : ∀ y, e0 (fun i => W.t * y i) = e0 y`. Introduce `y`. Establish `h1 : dc ((fun y => w' (fun i => W.t * y i)) - w') y = v y` using `by rw [hw'w, hdw]`.

Rewrite `h1` using `[dc_sub]`. Simplify using `only [Pi.sub_apply] at h1`. Rewrite `h1` using `[dc_comp w' (fun p => W.t * p) y]`. Simplify using `only [he0def, Pi.sub_apply, hvdef] at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `he0` using `W.inv_univ e0 he0S he0t`. Use `⟨-e0, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg y`. Simplify using `only [Pi.neg_apply]`. Rewrite using `[he0 g hg y]`.

Rewrite using `[dc_neg, he0def, dc_sub, dc_dc, sub_zero, hdx, neg_neg]`.
-/
theorem WData.inj (m : ℕ) (c : (Fin (m + 2) → P) → ℝ) (hc : InvS Set.univ c) (hdc : dc c = 0)
    (hres : ∀ g : Fin (m + 2) → G, c (fun i => W.ι (g i)) = 0)
    (hsl : ∀ g : Fin (m + 1) → G, prism W.ps c (fun i => W.ι (g i)) = 0) :
    ∃ e : (Fin (m + 1) → P) → ℝ, InvS Set.univ e ∧ c = dc e := by
  set S := Set.range W.ι with hSdef
  have hcS : InvS S c := fun g _ y => hc g trivial y
  have hprS : ∀ z ∈ S, W.pr z ∈ S := fun z _ => ⟨_, rfl⟩
  set x := prism W.pr c with hxdef
  have hxS : InvS S x := prism_inv W.pr S W.pr_mul c hcS
  have hdx : dc x = -c := by
    funext y
    have h := prism_dc W.pr m c y
    rw [hdc, prism_zero] at h
    have h0 : c (fun i => W.pr (y i)) = 0 := hres (fun i => W.ρ (y i))
    simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
    simpa using h
  have hx0 : ∀ g : Fin (m + 1) → G, x (fun i => W.ι (g i)) = 0 := fun g =>
    prism_eq_zero_of_set W.pr S hprS c _ (W.vanish_range c hres) (fun i => ⟨_, rfl⟩)
  have hxt : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) = 0 := by
    intro g
    rw [hxdef, prism_mul]
    have e1 : (fun z => W.t⁻¹ * W.pr (W.t * z)) = W.ps := by
      funext z; simp [WData.pr, WData.ps, W.ρt]
    have e2 : (fun z : Fin (m + 2) → P => c (fun i => W.t * z i)) = c := by
      funext z; exact hc _ trivial z
    rw [e1, e2]
    exact hsl g
  have hv0 : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) - x (fun i => W.ι (g i)) = 0 := by
    intro g; rw [hxt, hx0, sub_zero]
  have hdv : dc ((fun y => x (fun i => W.t * y i)) - x) = 0 := by
    rw [dc_sub]; funext z
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [dc_comp x (fun p => W.t * p) z, hdx]
    simp only [Pi.neg_apply]
    rw [hc _ trivial z]; ring
  have hvS : InvS S ((fun y => x (fun i => W.t * y i)) - x) := by
    intro g hg y
    simp only [Pi.sub_apply]
    have : (fun i => W.t * (g * y i)) = fun i => g * (W.t * y i) := by
      funext i; rw [← mul_assoc, ← mul_assoc, W.comm_range g hg]
    rw [this, hxS g hg, hxS g hg]
  cases m with
  | zero =>
    have hvz : ∀ y : Fin 1 → P, x (fun i => W.t * y i) = x y := by
      intro y
      have h := congrFun hdv (Fin.cons (W.ι 1) y)
      rw [dc_one] at h
      have h1 := hv0 (fun _ => 1)
      simp only [Pi.sub_apply, Pi.zero_apply] at h h1
      linarith
    refine ⟨-x, ?_, ?_⟩
    · have hx := W.inv_univ x hxS hvz
      intro g hg y; simp only [Pi.neg_apply]; rw [hx g hg y]
    · rw [dc_neg, hdx, neg_neg]
  | succ m' =>
    set v := (fun y => x (fun i => W.t * y i)) - x with hvdef
    set w := -prism W.pr v with hwdef
    have hdw : dc w = v := by
      funext y
      have h := prism_dc W.pr m' v y
      rw [hdv, prism_zero] at h
      have h0 : v (fun i => W.pr (y i)) = 0 := hv0 (fun i => W.ρ (y i))
      simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
      rw [hwdef, dc_neg, Pi.neg_apply, h, neg_neg]
    have hwS : InvS S w := by
      intro g hg y
      simp only [hwdef, Pi.neg_apply]
      rw [prism_inv W.pr S W.pr_mul v hvS g hg y]
    set lev : P → ℤ := fun z => W.ℓ (Additive.ofMul z) with hlevdef
    have hlev : ∀ z, lev (W.t * z) = lev z + 1 := by
      intro z; simp only [hlevdef, ofMul_mul, map_add, W.ℓt]; ring
    have hlevS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z := by
      rintro g ⟨g', rfl⟩ z; simp only [hlevdef, ofMul_mul, map_add, W.ℓι, zero_add]
    set w' := levSum W.t lev w with hw'def
    have hw'S : InvS S w' := levSum_inv W.t lev S hlevS W.comm_range w hwS
    have hw'w : (fun y => w' (fun i => W.t * y i)) - w' = w := by
      funext y; exact levSum_spec W.t lev hlev w y
    set e0 := x - dc w' with he0def
    have he0S : InvS S e0 := by
      intro g hg y
      simp only [he0def, Pi.sub_apply]
      rw [hxS g hg y, dc_inv S w' hw'S g hg y]
    have he0t : ∀ y, e0 (fun i => W.t * y i) = e0 y := by
      intro y
      have h1 : dc ((fun y => w' (fun i => W.t * y i)) - w') y = v y := by rw [hw'w, hdw]
      rw [dc_sub] at h1
      simp only [Pi.sub_apply] at h1
      rw [dc_comp w' (fun p => W.t * p) y] at h1
      simp only [he0def, Pi.sub_apply, hvdef] at h1 ⊢
      linarith
    have he0 := W.inv_univ e0 he0S he0t
    refine ⟨-e0, ?_, ?_⟩
    · intro g hg y; simp only [Pi.neg_apply]; rw [he0 g hg y]
    · rw [dc_neg, he0def, dc_sub, dc_dc, sub_zero, hdx, neg_neg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
