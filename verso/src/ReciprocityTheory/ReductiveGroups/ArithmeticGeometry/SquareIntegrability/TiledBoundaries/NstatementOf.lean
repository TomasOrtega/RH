import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.PointwiseNormSqPullbackTensorEqProd

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `hF.1.continuous`.
-/
private theorem continuous_of_mem_Sec (X : PT E) {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Continuous F :=
  hF.1.continuous

/- English proof (translation)
Establish `hπc : Continuous π` using `LinearMap.continuous_of_finiteDimensional π`. Use `show Continuous (fun v : Fin n → Vsp X.dim => ∏ k, s fun _ => π (v k))`. Conclude with `continuous_finset_prod _ fun k _ => hs.comp (continuous_pi fun _ => hπc.comp (continuous_apply k))`.
-/
private theorem continuous_s0_of_continuous (X : PT E) {n : ℕ} (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : Continuous s) : Continuous (s0 X (n := n) π s) := by
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  show Continuous (fun v : Fin n → Vsp X.dim => ∏ k, s fun _ => π (v k))
  exact continuous_finset_prod _ fun k _ =>
    hs.comp (continuous_pi fun _ => hπc.comp (continuous_apply k))

/- English proof (translation)
Establish `hπc : Continuous π` using `LinearMap.continuous_of_finiteDimensional π`. Establish `hsc : Continuous s` using `continuous_of_mem_Sec X hs`. Establish `hF0 : s0 X (n` using `n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs`. Establish `hgc : Continuous (X.ptN2 q (s0 X (n` using `n) π s)) := continuous_pointNormSq_quotient X q (continuous_s0_of_continuous X π hsc)`. Establish `hc1 : Continuous (X.ptN2 1 s)` using `continuous_pointNormSq_quotient X 1 hsc`.

Establish `hgc1 : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => w))` using `hc1.comp (continuous_pi fun _ => continuous_id)`. Establish `hfc : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => π w))` using `hgc1.comp hπc`. Establish `hper : ∀ γ ∈ X.L, ∀ v : Vsp X.dim, X.ptN2 1 s (fun _ => v + γ) = X.ptN2 1 s (fun _ => v)` using `fun γ hγ v => pointwiseNormSq_add_period (X := X) hs (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)`. Establish `e1 : X.l2 q (X.U q b (s0 X π s)) = ⨍ v in X.fd n, X.ptN2 q (s0 X (n` using `n) π s) v := by`. Establish `key : (⨍ v in X.fd n, X.ptN2 q (s0 X (n` using `n) π s) (v - b)) = ⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v := hT E X n ℝ (X.ptN2 q (s0 X (n := n) π s)) hgc (fun γ hγ v => pointwiseNormSq_add_period (X := X) hF0 hγ v) b`.

Unfold `PT.l2`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `pointwiseNormSq_translate (X := X) q b _ v`.

Establish `e2 : (⨍ v in X.fd n, X.ptN2 q (s0 X (n` using `n) π s) v) = (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n := by`. Establish `key : (⨍ v in X.fd n, ∏ k, X.ptN2 1 s (fun _ => π (v k))) = (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n` using `hF E X n (fun w => X.ptN2 1 s (fun _ => π w)) hfc`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `pointwiseNormSq_pullback_tensor_eq_prod X hπ s v`. Establish `e3 : (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) = ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w)` using `hP E X q π hq hπ (fun w => X.ptN2 1 s (fun _ => w)) hgc1 hper`. Establish `e4 : X.l2 1 s = ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w)`. Establish `key : (⨍ v in X.fd 1, ∏ k, X.ptN2 1 s (fun _ => v k)) = (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w)) ^ 1` using `hF E X 1 (fun w => X.ptN2 1 s (fun _ => w)) hgc1`. Use `Eq.trans ?_ (key.trans (pow_one _))` and prove the remaining obligations.

Unfold `PT.l2`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[Fin.prod_univ_one]`. Conclude with `congrArg (X.ptN2 1 s) (funext fun i => congrArg v (Subsingleton.elim i 0))`.

Rewrite using `[e1, e2, e3, e4]`.
-/
theorem norm_part (hT : StepT) (hF : StepF) (hP : StepP) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (b : Fin n → Vsp X.dim) :
    X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n := by
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hsc : Continuous s := continuous_of_mem_Sec X hs
  have hF0 : s0 X (n := n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs
  have hgc : Continuous (X.ptN2 q (s0 X (n := n) π s)) := continuous_pointNormSq_quotient X q (continuous_s0_of_continuous X π hsc)
  have hc1 : Continuous (X.ptN2 1 s) := continuous_pointNormSq_quotient X 1 hsc
  have hgc1 : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => w)) :=
    hc1.comp (continuous_pi fun _ => continuous_id)
  have hfc : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => π w)) := hgc1.comp hπc
  have hper : ∀ γ ∈ X.L, ∀ v : Vsp X.dim, X.ptN2 1 s (fun _ => v + γ) = X.ptN2 1 s (fun _ => v) :=
    fun γ hγ v => pointwiseNormSq_add_period (X := X) hs (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)
  have e1 : X.l2 q (X.U q b (s0 X π s)) = ⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v := by
    have key : (⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) (v - b)) =
        ⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v :=
      hT E X n ℝ (X.ptN2 q (s0 X (n := n) π s)) hgc
        (fun γ hγ v => pointwiseNormSq_add_period (X := X) hF0 hγ v) b
    unfold PT.l2
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact pointwiseNormSq_translate (X := X) q b _ v
  have e2 : (⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v) =
      (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n := by
    have key : (⨍ v in X.fd n, ∏ k, X.ptN2 1 s (fun _ => π (v k))) =
        (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n :=
      hF E X n (fun w => X.ptN2 1 s (fun _ => π w)) hfc
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact pointwiseNormSq_pullback_tensor_eq_prod X hπ s v
  have e3 : (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) =
      ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w) :=
    hP E X q π hq hπ (fun w => X.ptN2 1 s (fun _ => w)) hgc1 hper
  have e4 : X.l2 1 s = ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w) := by
    have key : (⨍ v in X.fd 1, ∏ k, X.ptN2 1 s (fun _ => v k)) =
        (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w)) ^ 1 :=
      hF E X 1 (fun w => X.ptN2 1 s (fun _ => w)) hgc1
    refine Eq.trans ?_ (key.trans (pow_one _))
    unfold PT.l2
    congr 1
    funext v
    rw [Fin.prod_univ_one]
    exact congrArg (X.ptN2 1 s) (funext fun i => congrArg v (Subsingleton.elim i 0))
  rw [e1, e2, e3, e4]

/- English proof (translation)
Assume the negation of the conclusion as `hI`. Apply `hne` to reduce the goal to its premises. Establish `hF0 : s0 X (n` using `n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs`. Establish `hUb : X.U q b (s0 X π s) ∈ X.Sec q n` using `nA_U_mem (X := X) hF0 (hK.1 b hb)`. Establish `hUb' : X.U q b' (s0 X π s) ∈ X.Sec q n` using `nA_U_mem (X := X) hF0 (hK.1 b' hb')`.

Establish `hinv : ∀ (k : Fin n → Vsp X.dim) {F G : (Fin n → Vsp X.dim) → ℂ}, F ∈ X.Sec q n → G ∈ X.Sec q n → X.l2ip q (X.U q k F) (X.U q k G) = X.l2ip q F G`. Introduce `k F G hF hG`. Establish `key` using `hT E X n ℂ (fun v => F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) (cont_ip q (continuous_of_mem_Sec X hF) (continuous_of_mem_Sec X hG)) (fun γ hγ v => nA_ip_periodic (X := X) hF hG hγ v) k`. Unfold `PT.l2ip`. Use `Eq.trans ?_ key` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `nA_ip_U (X := X) q k F G v`. Establish `hUs0 : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) → X.U q k (s0 X π s) = fun v => (∏ j, (X.eps (π (k j)) : ℂ)) * s0 X π s v` using `fun k hk => funext fun v => translate_pullbackSection (X := X) hπ hs hk v`. Establish `hshift : ∀ (a k : Fin n → Vsp X.dim), (∀ j, π (k j) ∈ X.L) → X.U q k (X.U q a (s0 X π s)) = fun v => (cexp ((q : ℂ) * Real.pi * (HC a k - HC k a)) * ∏ j, (X.eps (π (k j)) : ℂ)) * X.U q a (s0 X π s) v`.

Introduce `a k hk`. Use function extensionality and compare the values at `v`. Rewrite using `[nA_U_comm (X := X) q k a _ v, hUs0 k hk, nA_U_smul (X := X) q a _ (s0 X π s)]`. Apply the tactic sequence `try dsimp only`. Expand and normalize the polynomial expressions, which then agree.

Establish `hphase : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) → cexp ((q : ℂ) * Real.pi * (HC (b - b') k - HC k (b - b'))) = 1`. Introduce `k hk`. Establish `hε2 : (∏ j, (X.eps (π (k j)) : ℂ)) * (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = 1`. Establish `c1 : (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = ∏ j, (X.eps (π (k j)) : ℂ)` using `nA_epsprod_conj (X := X) (fun j => π (k j))`. Establish `c2 : (∏ j, (X.eps (π (k j)) : ℂ)) ^ 2 = 1` using `nA_epsprod_sq (X := X) (γ := fun j => π (k j)) hk`.

Rewrite using `[c1, ← sq, c2]`. Establish `h1` using `hinv k hUb hUb'`. Rewrite `h1` using `[hshift b k hk, hshift b' k hk, l2Inner_smul]`. Establish `hc` using `mul_right_cancel₀ hI (h1.trans (one_mul _).symm)`. Establish `hw : (starRingEnd ℂ) ((q : ℂ) * Real.pi * (HC b' k - HC k b')) = (q : ℂ) * Real.pi * (HC k b' - HC b' k)`.

Rewrite using `[map_mul, map_mul, map_sub, nA_HC_conj, nA_HC_conj, map_natCast, Complex.conj_ofReal]`. Rewrite using `[← hc, map_mul, show ∀ a e c f : ℂ, a * e * (c * f) = a * c * (e * f) from fun a e c f => by ring, hε2, mul_one, ← Complex.exp_conj, hw, ← Complex.exp_add, nA_HC_sub_left, nA_HC_sub_right]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : ∀ j, π ((b - b') j) ∈ X.L`.

Introduce `j`. Apply `hDual E X (π ((b - b') j))` to reduce the goal to its premises. Introduce `y hy`. Take `⟨z, rfl⟩` from `(pi_bij X hq hπ).2 y`. Establish `hk : ∀ i, π ((Pi.single j z : Fin n → Vsp X.dim) i) ∈ X.L`.

Introduce `i`. Break down `eq_or_ne i j with rfl | h` into its components or cases. Rewrite using `[Pi.single_eq_same]`. Conclude with `hy`. Rewrite using `[Pi.single_eq_of_ne h, map_zero]`.

Conclude with `X.L.zero_mem`. Establish `hexp` using `hphase (Pi.single j z) hk`. Establish `hHC : HC (b - b') (Pi.single j z) = Hf ((b - b') j) z`. Unfold `HC`. Rewrite using `[Finset.sum_eq_single j]`.

Rewrite using `[Pi.single_eq_same]`. Introduce `i _ hij`. Rewrite using `[Pi.single_eq_of_ne hij]`. Simplify using `[Hf]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`. Rewrite `hexp` using `[← nA_HC_conj (b - b') (Pi.single j z), hHC]`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 hexp`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[Complex.sub_conj]`.

Establish `key : (((q : ℝ) * (Hf ((b - b') j) z).im : ℝ) : ℂ) = (m : ℂ)`. Apply `mul_right_cancel₀ Complex.two_pi_I_ne_zero` to reduce the goal to its premises. Rewrite using `[← hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `key' : (q : ℝ) * (Hf ((b - b') j) z).im = m` using `by exact_mod_cast key`. Rewrite using `[hπ.2.2.1, ← key']`. Simplify using `[Complex.mul_im]`. Conclude with `(hK.2 b (hK.1 b hb)).unique ⟨hb, fun k => by rw [sub_self, map_zero]; exact X.L.zero_mem⟩ ⟨hb', fun k => hmem k⟩`.
-/
theorem orth_part (hT : StepT) (hDual : StepDual) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    {b b' : Fin n → Vsp X.dim} (hb : b ∈ K) (hb' : b' ∈ K) (hne : b ≠ b') :
    X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0 := by
  by_contra hI
  apply hne
  have hF0 : s0 X (n := n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs
  have hUb : X.U q b (s0 X π s) ∈ X.Sec q n := nA_U_mem (X := X) hF0 (hK.1 b hb)
  have hUb' : X.U q b' (s0 X π s) ∈ X.Sec q n := nA_U_mem (X := X) hF0 (hK.1 b' hb')

  have hinv : ∀ (k : Fin n → Vsp X.dim) {F G : (Fin n → Vsp X.dim) → ℂ}, F ∈ X.Sec q n →
      G ∈ X.Sec q n → X.l2ip q (X.U q k F) (X.U q k G) = X.l2ip q F G := by
    intro k F G hF hG
    have key := hT E X n ℂ
      (fun v => F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ))
      (cont_ip q (continuous_of_mem_Sec X hF) (continuous_of_mem_Sec X hG))
      (fun γ hγ v => nA_ip_periodic (X := X) hF hG hγ v) k
    unfold PT.l2ip
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact nA_ip_U (X := X) q k F G v
  have hUs0 : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) →
      X.U q k (s0 X π s) = fun v => (∏ j, (X.eps (π (k j)) : ℂ)) * s0 X π s v :=
    fun k hk => funext fun v => translate_pullbackSection (X := X) hπ hs hk v
  have hshift : ∀ (a k : Fin n → Vsp X.dim), (∀ j, π (k j) ∈ X.L) →
      X.U q k (X.U q a (s0 X π s)) =
        fun v => (cexp ((q : ℂ) * Real.pi * (HC a k - HC k a)) * ∏ j, (X.eps (π (k j)) : ℂ)) *
          X.U q a (s0 X π s) v := by
    intro a k hk
    funext v
    rw [nA_U_comm (X := X) q k a _ v, hUs0 k hk, nA_U_smul (X := X) q a _ (s0 X π s)]
    try dsimp only
    ring

  have hphase : ∀ k : Fin n → Vsp X.dim, (∀ j, π (k j) ∈ X.L) →
      cexp ((q : ℂ) * Real.pi * (HC (b - b') k - HC k (b - b'))) = 1 := by
    intro k hk
    have hε2 : (∏ j, (X.eps (π (k j)) : ℂ)) * (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = 1 := by
      have c1 : (starRingEnd ℂ) (∏ j, (X.eps (π (k j)) : ℂ)) = ∏ j, (X.eps (π (k j)) : ℂ) :=
        nA_epsprod_conj (X := X) (fun j => π (k j))
      have c2 : (∏ j, (X.eps (π (k j)) : ℂ)) ^ 2 = 1 :=
        nA_epsprod_sq (X := X) (γ := fun j => π (k j)) hk
      rw [c1, ← sq, c2]
    have h1 := hinv k hUb hUb'
    rw [hshift b k hk, hshift b' k hk, l2Inner_smul] at h1
    have hc := mul_right_cancel₀ hI (h1.trans (one_mul _).symm)
    have hw : (starRingEnd ℂ) ((q : ℂ) * Real.pi * (HC b' k - HC k b')) =
        (q : ℂ) * Real.pi * (HC k b' - HC b' k) := by
      rw [map_mul, map_mul, map_sub, nA_HC_conj, nA_HC_conj, map_natCast, Complex.conj_ofReal]
    rw [← hc, map_mul,
      show ∀ a e c f : ℂ, a * e * (c * f) = a * c * (e * f) from fun a e c f => by ring,
      hε2, mul_one, ← Complex.exp_conj, hw, ← Complex.exp_add, nA_HC_sub_left, nA_HC_sub_right]
    congr 1
    ring

  have hmem : ∀ j, π ((b - b') j) ∈ X.L := by
    intro j
    apply hDual E X (π ((b - b') j))
    intro y hy
    obtain ⟨z, rfl⟩ := (pi_bij X hq hπ).2 y
    have hk : ∀ i, π ((Pi.single j z : Fin n → Vsp X.dim) i) ∈ X.L := by
      intro i
      rcases eq_or_ne i j with rfl | h
      · rw [Pi.single_eq_same]; exact hy
      · rw [Pi.single_eq_of_ne h, map_zero]; exact X.L.zero_mem
    have hexp := hphase (Pi.single j z) hk
    have hHC : HC (b - b') (Pi.single j z) = Hf ((b - b') j) z := by
      unfold HC
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij]
        simp [Hf]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [← nA_HC_conj (b - b') (Pi.single j z), hHC] at hexp
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
    refine ⟨m, ?_⟩
    rw [Complex.sub_conj] at hm
    have key : (((q : ℝ) * (Hf ((b - b') j) z).im : ℝ) : ℂ) = (m : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      rw [← hm]
      push_cast
      ring
    have key' : (q : ℝ) * (Hf ((b - b') j) z).im = m := by exact_mod_cast key
    rw [hπ.2.2.1, ← key']
    simp [Complex.mul_im]
  exact (hK.2 b (hK.1 b hb)).unique
    ⟨hb, fun k => by rw [sub_self, map_zero]; exact X.L.zero_mem⟩ ⟨hb', fun k => hmem k⟩

/- English proof (translation)
Take `⟨f, hf⟩ : ∃ f : ↥K → (Fin n → Vsp X.dim) → ℂ, ∀ i, f i = X.U q i.1 (s0 X π s)` from `⟨fun i => X.U q i.1 (s0 X π s), fun _ => rfl⟩`. Establish `hcont : ∀ i, Continuous (f i)` using `fun i => by`. Rewrite using `[hf]`. Conclude with `continuous_of_mem_Sec X (h1 i.1 i.2)`. Establish `hpos : 0 < X.l2 1 s` using `hPos E X 1 1 s hs hs0`.

Establish `hli : LinearIndependent ℂ f`. Rewrite using `[linearIndependent_iff']`. Introduce `t g hg i hi`. Establish `hfun : (fun v => ∑ j ∈ t, g j * f j v) = 0`. Rewrite using `[← hg]`.

Use function extensionality and compare the values at `v`. Simplify using `[Finset.sum_apply]`. Establish `e` using `l2Inner_sum_left hI X q t g f (f i) hcont (hcont i)`. Rewrite `e` using `[hfun, l2Inner_zero_left, Finset.sum_eq_single i]`. Rewrite `e` using `[l2Inner_self, hf i, h3 i.1 i.2]`.

Conclude with `(mul_eq_zero.1 e.symm).resolve_right (Complex.ofReal_ne_zero.2 (pow_pos hpos n).ne')`. Introduce `j _ hji`. Rewrite using `[hf j, hf i, h2 j.1 j.2 i.1 i.2 (fun h => hji (Subtype.ext h)), mul_zero]`. Introduce `h`. Conclude with `absurd hi h`.

Establish `hrange : Set.range f = (fun b => X.U q b (s0 X π s)) '' (K : Set _)`. Use extensionality with `x`. Simplify using `[hf]`. Use `haveI : FiniteDimensional ℂ (X.Sec q n) := (hD E X q n hq).1`. Establish `hle : Submodule.span ℂ (Set.range f) ≤ X.Sec q n`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hf]`. Conclude with `h1 i.1 i.2`. Establish `heq` using `Submodule.eq_of_le_of_finrank_le hle (by`.

Rewrite using `[finrank_span_eq_card hli, Fintype.card_coe]`. Conclude with `(hD E X q n hq).2.trans (hKc E X q n π hq hπ K hK))`. Rewrite using `[← hrange]`. Conclude with `heq.ge`.
-/
theorem span_part (hI : StepI) (hPos : StepPos) (hKc : StepK) (hD : StepD) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (hs0 : s ≠ 0) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    (h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n)
    (h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0)
    (h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n) :
    X.Sec q n ≤ Submodule.span ℂ ((fun b => X.U q b (s0 X π s)) '' (K : Set _)) := by
  obtain ⟨f, hf⟩ : ∃ f : ↥K → (Fin n → Vsp X.dim) → ℂ, ∀ i, f i = X.U q i.1 (s0 X π s) :=
    ⟨fun i => X.U q i.1 (s0 X π s), fun _ => rfl⟩
  have hcont : ∀ i, Continuous (f i) := fun i => by
    rw [hf]; exact continuous_of_mem_Sec X (h1 i.1 i.2)
  have hpos : 0 < X.l2 1 s := hPos E X 1 1 s hs hs0

  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have hfun : (fun v => ∑ j ∈ t, g j * f j v) = 0 := by
      rw [← hg]; funext v; simp [Finset.sum_apply]
    have e := l2Inner_sum_left hI X q t g f (f i) hcont (hcont i)
    rw [hfun, l2Inner_zero_left, Finset.sum_eq_single i] at e
    · rw [l2Inner_self, hf i, h3 i.1 i.2] at e
      exact (mul_eq_zero.1 e.symm).resolve_right (Complex.ofReal_ne_zero.2 (pow_pos hpos n).ne')
    · intro j _ hji
      rw [hf j, hf i, h2 j.1 j.2 i.1 i.2 (fun h => hji (Subtype.ext h)), mul_zero]
    · intro h; exact absurd hi h
  have hrange : Set.range f = (fun b => X.U q b (s0 X π s)) '' (K : Set _) := by
    ext x; simp [hf]
  haveI : FiniteDimensional ℂ (X.Sec q n) := (hD E X q n hq).1
  have hle : Submodule.span ℂ (Set.range f) ≤ X.Sec q n := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hf]; exact h1 i.1 i.2

  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [finrank_span_eq_card hli, Fintype.card_coe]
    exact (hD E X q n hq).2.trans (hKc E X q n π hq hπ K hK))
  rw [← hrange]
  exact heq.ge

/- English proof (translation)
Introduce `E _ _ _ X q n π hq hπ s hs hs0 K hK`. Establish `hS` using `pullbackSection_mem_thetaSpace X (n := n) hπ hs`. Establish `h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n` using `fun b hb => nA_U_mem X hS (hK.1 b hb)`. Establish `h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0` using `fun b hb b' hb' hne => orth_part hT hDual X hq hπ hs hK hb hb' hne`. Establish `h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n` using `fun b _ => norm_part hT hF hP X hq hπ hs b`.

Conclude with `⟨h1, h2, h3, span_part hI hPos hKc hD X hq hπ hs hs0 hK h1 h2 h3⟩`.
-/
theorem nstatement_of (hT : StepT) (hI : StepI) (hF : StepF) (hP : StepP) (hPos : StepPos)
    (hDual : StepDual) (hKc : StepK) (hD : StepD) : NStatement := by
  intro E _ _ _ X q n π hq hπ s hs hs0 K hK
  have hS := pullbackSection_mem_thetaSpace X (n := n) hπ hs
  have h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n := fun b hb => nA_U_mem X hS (hK.1 b hb)
  have h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' →
      X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0 :=
    fun b hb b' hb' hne => orth_part hT hDual X hq hπ hs hK hb hb' hne
  have h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n :=
    fun b _ => norm_part hT hF hP X hq hπ hs b
  exact ⟨h1, h2, h3, span_part hI hPos hKc hD X hq hπ hs hs0 hK h1 h2 h3⟩

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
