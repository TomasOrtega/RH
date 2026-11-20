import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespondStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Move

/- English proof (translation)
Set `f : R → Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂` to `fun y => QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Use `QuotientAddGroup.eq.1 hxy` as an intermediate fact.

Rewrite `this` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h3 : φ (y.1 - x.1) ∈ Λ₁` using `by simpa [map_sub, neg_add_eq_sub] using this`. Conclude with `Subtype.ext (hR.2.1 _ y.2 _ x.2 ((h₁ _).1 h3)).symm`. Introduce `q`. Take `⟨v, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Take `⟨y, hy, hv⟩` from `(h₂ _).1 v.2`. Take `⟨x, hx, hxy⟩` from `hR.2.2 y hy`. Use `⟨⟨x, hx⟩, QuotientAddGroup.eq.2 ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Use `(h₁ _).2 hxy` as an intermediate fact.

Simplify `this` using `[map_sub, neg_add_eq_sub, hv]`. Set `e` to `Equiv.ofBijective f hf`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.index, ← Nat.card_congr e]`. Simplify using the standard rewrite rules.

Rewrite using `[← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort R]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `hq : (QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = QuotientAddGroup.mk (Quotient.out (e y))` using `(QuotientAddGroup.out_eq' (e y)).symm`. Establish `h3` using `QuotientAddGroup.eq.1 hq`. Rewrite `h3` using `[AddSubgroup.mem_addSubgroupOf]`.

Use `hF _ ((h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩) _ (Subtype.property _) h3` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem finsum_eq_sum_reps {G V : Type} [AddCommGroup G] [AddCommGroup V] (φ : G →+ V) (M M' : AddSubgroup G)
    (Λ₁ Λ₂ : AddSubgroup V) (h₁ : ∀ y, φ y ∈ Λ₁ ↔ y ∈ M) (h₂ : ∀ v, v ∈ Λ₂ ↔ ∃ y ∈ M', φ y = v) (R : Finset G)
    (hR : IsReps M M' R) (F : V → ℂ) (hF : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → F (x + l) = F x) :
    (Λ₁.addSubgroupOf Λ₂).index = R.card ∧
      ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, F ((Quotient.out q : Λ₂) : V) = ∑ y ∈ R, F (φ y) := by
  classical
  let f : R → Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := fun y => QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := QuotientAddGroup.eq.1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have h3 : φ (y.1 - x.1) ∈ Λ₁ := by simpa [map_sub, neg_add_eq_sub] using this
      exact Subtype.ext (hR.2.1 _ y.2 _ x.2 ((h₁ _).1 h3)).symm
    · intro q
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨y, hy, hv⟩ := (h₂ _).1 v.2
      obtain ⟨x, hx, hxy⟩ := hR.2.2 y hy
      refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.2 ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have := (h₁ _).2 hxy
      simpa [map_sub, neg_add_eq_sub, hv] using this
  let e := Equiv.ofBijective f hf
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  · rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq : (QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
        QuotientAddGroup.mk (Quotient.out (e y)) := (QuotientAddGroup.out_eq' (e y)).symm
    have h3 := QuotientAddGroup.eq.1 hq
    rw [AddSubgroup.mem_addSubgroupOf] at h3
    have := hF _ ((h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩) _ (Subtype.property _) h3
    rw [← this]
    congr 1
    simp

/- English proof (translation)
Establish `hx' : x ∈ dualLat H Λ` using `by rw [hs]; exact hx`. Take `⟨m, hm⟩` from `hx' l hl`. Establish `h1` using `hF (z + x)`. Establish `h2 : H l x = H x l - 2 * Complex.I * m`. Rewrite using `[hH x l]`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `only [altE] at hm`. Simplify using `[hm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hα.2 x hx l hl, hm]`. Simplify using `only [opU] at h1 ⊢`. Rewrite using `[← h1, ← add_assoc]`. Establish `h3 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * H z (x + l) - (Real.pi : ℂ) * H (x + l) (x + l) / 2) = Complex.exp (-(Real.pi : ℂ) * H (z + x) l - (Real.pi : ℂ) * H l l / 2) * Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, LinearMap.add_apply, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(α x * α l * F (z + x + l)) * h3`.
-/
theorem op_add {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (Λ : AddSubgroup V)
    (hs : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) (F : V → ℂ) (x l : V) (hx : x ∈ Λ) (hl : l ∈ Λ)
    (hF : ∀ z, α l * opU H l F z = F z) (z : V) : α (x + l) * opU H (x + l) F z = α x * opU H x F z := by
  have hx' : x ∈ dualLat H Λ := by rw [hs]; exact hx
  obtain ⟨m, hm⟩ := hx' l hl
  have h1 := hF (z + x)
  have h2 : H l x = H x l - 2 * Complex.I * m := by
    rw [hH x l]
    apply Complex.ext
    · simp
    · simp only [altE] at hm
      simp [hm]; ring
  rw [hα.2 x hx l hl, hm]
  simp only [opU] at h1 ⊢
  rw [← h1, ← add_assoc]
  have h3 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * H z (x + l) - (Real.pi : ℂ) * H (x + l) (x + l) / 2) =
      Complex.exp (-(Real.pi : ℂ) * H (z + x) l - (Real.pi : ℂ) * H l l / 2) *
        Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [map_add, LinearMap.add_apply, h2]
    push_cast
    ring
  linear_combination (α x * α l * F (z + x + l)) * h3

/- English proof (translation)
Establish `h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1`. Rewrite using `[two_mul, Complex.exp_add]`. Apply the tactic sequence `rcases h with h | h <;> simp [h]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h2`. Establish `hq : (q : ℂ) = n`.

Establish `h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `Complex.two_pi_I_ne_zero`. Apply `mul_left_cancel₀ h0` to reduce the goal to its premises. Take the linear combination `hn`. Establish `hq' : q = n` using `by exact_mod_cast hq`. Rewrite using `[hq, hq', round_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
theorem neg_one_zpow_round (q : ℝ)
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 ∨ Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = -1) :
    (-1 : ℂ) ^ (round q) = Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
  have h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1 := by
    rw [two_mul, Complex.exp_add]
    rcases h with h | h <;> simp [h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hq : (q : ℂ) = n := by
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h0
    linear_combination hn
  have hq' : q = n := by exact_mod_cast hq
  rw [hq, hq', round_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Introduce `x y`. Simplify using `[Formalism.L2.Ker.HV, map_sum, mul_comm]`.
-/
theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

/- English proof (translation)
Introduce `x y h`. Take `⟨τ⟩` from `‹Nonempty ι›`. Use `(Pi.basisFun E (Fin a)).ext fun j => funext fun i => ?_` and prove the remaining obligations. Use `congrFun (congrFun (congrFun h τ) i) j` as an intermediate fact. Simplify using `only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this`.

Simplify using `using (emb τ).injective (mul_left_cancel₀ hδ this)`.
-/
theorem embH_inj {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine (Pi.basisFun E (Fin a)).ext fun j => funext fun i => ?_
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

/- English proof (translation)
Introduce `D X s cc δ B χ cD a b N N' N'' _ hs hE ha hb hL hN hN' hN'' R hR z`. Take `⟨hδ, hτ, -, -, -, hL⟩` from `hL`. Take `⟨t1, t2, t3, -⟩` from `GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs`. Use `set A := ambOf s B χ cD with hA`. Use `letI := D.host.cmStar`.

Establish `key` using `congrFun (hE.2.1 a b ⟨s.lat N, (t2 N N' ha hb hN hN').2.2.1⟩ ⟨s.lat N', (t2 N N' ha hb hN hN').2.2.2⟩ ⟨s.lat N'', (t2 N N'' ha hb hN hN'').2.2.2⟩ ha hb) fun τ => z (s.iT.symm τ)`. Use `key.trans (congrArg₂ (· * ·) rfl ?_)` and prove the remaining obligations. Set `φ : HomE X.E a b →+ TaylorLogMetric.VC D a b` to `{ toFun := fun y τ => emb A y (s.iT.symm τ) map_zero' := by funext τ; simp [emb] map_add' := fun x y => by funext τ; simp [emb] }`. Establish `hφ : ∀ y, (fun τ => φ y (s.iT τ)) = emb A y` using `fun y => by funext τ; simp [φ]`. Establish `hmem : ∀ (M : Submodule (𝓞 X.E) (Sp X.E b)) v, v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat M) ↔ ∃ y ∈ (per A N M).toAddSubgroup, φ y = v`.

Introduce `M v`. Rewrite using `[t1]`. Use `exists_congr fun y => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Use `congrFun h (s.iT.symm τ)` as an intermediate fact.

Simplify using `only [Equiv.apply_symm_apply] at this`. Conclude with `this`. Rewrite using `[← h, hφ]`. Both sides reduce to the same expression. Establish `h₁ : ∀ y, φ y ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ y ∈ (per A N N').toAddSubgroup`.

Introduce `y`. Rewrite using `[hmem]`. Use `⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩` and prove the remaining obligations. Establish `h' : emb A x = emb A y` using `by rw [← hφ, ← hφ, h]`. Conclude with `embH_inj _ hδ h' ▸ hx`.

Establish `hW : ∀ v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N''), TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N')) (fun τ => z (s.iT.symm τ)) = alV A.d A.sc (fun τ => …`. Introduce `v hv`. Use `congrArg₂ (· * ·) ?_ ?_` and prove the remaining obligations. Establish `h` using `(hL N N'' hN hN'').2.2.1 _ ((t1 N N'' v).1 hv)`. Unfold `TaylorLogMetric.al`.

Rewrite using `[t3]`. Conclude with `neg_one_zpow_round _ h`. Unfold `TaylorLogMetric.U opU`. Rewrite using `[t3, t3]`. Simplify using `only [Equiv.symm_apply_apply]`.

Use `congrArg₂ (· * ·) ?_ rfl` and prove the remaining obligations. Use `congrArg (B.eNat χ a b (s.lat N) (s.lat N')) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Take `⟨e1, e2⟩` from `finsum_eq_sum_reps φ _ _ _ _ h₁ (hmem N'') R hR (fun v => TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N')) (fun τ => z (s.iT.symm τ))) (by`.

Introduce `x hx l hl hl'`. Rewrite using `[hW _ (add_mem hx hl), hW _ hx]`. Conclude with `op_add _ (isHerm_HV _) _ _ (hL N N'' hN hN'').2.1 (hL N N'' hN hN'').2.2 _ _ _ ((t1 N N'' x).1 hx) ((t1 N N'' l).1 hl) ((hL N N' hN hN').1 _ ((t1 N N' l).1 hl')) z)`. Unfold `TaylorLogMetric.Iop`. Use `congrArg₂ (· * ·) ?_ (e2.trans (Finset.sum_congr rfl fun y hy => ?_))` and prove the remaining obligations.

Rewrite using `[← e1]`. Rewrite using `[hW _ ((hmem N'' _).2 ⟨y, hR.1 y hy, rfl⟩), hφ]`. Both sides reduce to the same expression.
-/
theorem move : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → B.EqP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ → IsSdLat N → IsSdLat N' → IsSdLat N'' → ∀ R : Finset (HomE X.E a b), IsReps (per (ambOf s B χ cD) N N').toAddSubgroup (per (ambOf s B χ cD) N N'').toAddSubgroup R → ∀ z, (ambOf s B χ cD).e a b N N'' z = χ (TaylorLogMetric.detId D (s.lat N') (s.lat N'')) ^ (-((a / 2 : ℕ) : ℤ)) * (((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ y ∈ R, Wx (ambOf s B χ cD) y ((ambOf s B χ cD).e a b N N') z) := by
  intro D X s cc δ B χ cD a b N N' N'' _ hs hE ha hb hL hN hN' hN'' R hR z
  obtain ⟨hδ, hτ, -, -, -, hL⟩ := hL
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.fieldIso_lattices_form_taylor_correspond D X s cc δ B χ cD a b hs
  set A := ambOf s B χ cD with hA
  letI := D.host.cmStar
  have key := congrFun (hE.2.1 a b ⟨s.lat N, (t2 N N' ha hb hN hN').2.2.1⟩ ⟨s.lat N', (t2 N N' ha hb hN hN').2.2.2⟩
    ⟨s.lat N'', (t2 N N'' ha hb hN hN'').2.2.2⟩ ha hb) fun τ => z (s.iT.symm τ)
  refine key.trans (congrArg₂ (· * ·) rfl ?_)
  let φ : HomE X.E a b →+ TaylorLogMetric.VC D a b :=
    { toFun := fun y τ => emb A y (s.iT.symm τ)
      map_zero' := by funext τ; simp [emb]
      map_add' := fun x y => by funext τ; simp [emb] }
  have hφ : ∀ y, (fun τ => φ y (s.iT τ)) = emb A y := fun y => by funext τ; simp [φ]
  have hmem : ∀ (M : Submodule (𝓞 X.E) (Sp X.E b)) v, v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat M) ↔
      ∃ y ∈ (per A N M).toAddSubgroup, φ y = v := by
    intro M v
    rw [t1]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext τ
      have := congrFun h (s.iT.symm τ)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    · rw [← h, hφ]; rfl
  have h₁ : ∀ y, φ y ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ y ∈ (per A N N').toAddSubgroup := by
    intro y
    rw [hmem]
    refine ⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
    have h' : emb A x = emb A y := by rw [← hφ, ← hφ, h]
    exact embH_inj _ hδ h' ▸ hx
  have hW : ∀ v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N''),
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ)) =
      alV A.d A.sc (fun τ => v (s.iT τ)) * opU (HV A.sc) (fun τ => v (s.iT τ)) (A.e a b N N') z := by
    intro v hv
    refine congrArg₂ (· * ·) ?_ ?_
    · have h := (hL N N'' hN hN'').2.2.1 _ ((t1 N N'' v).1 hv)
      unfold TaylorLogMetric.al
      rw [t3]
      exact neg_one_zpow_round _ h
    · unfold TaylorLogMetric.U opU
      rw [t3, t3]
      simp only [Equiv.symm_apply_apply]
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg (B.eNat χ a b (s.lat N) (s.lat N')) ?_
      funext τ
      simp
  obtain ⟨e1, e2⟩ := finsum_eq_sum_reps φ _ _ _ _ h₁ (hmem N'') R hR
    (fun v => TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ))) (by
      intro x hx l hl hl'
      rw [hW _ (add_mem hx hl), hW _ hx]
      exact op_add _ (isHerm_HV _) _ _ (hL N N'' hN hN'').2.1 (hL N N'' hN hN'').2.2 _ _ _ ((t1 N N'' x).1 hx)
        ((t1 N N'' l).1 hl) ((hL N N' hN hN').1 _ ((t1 N N' l).1 hl')) z)
  unfold TaylorLogMetric.Iop
  refine congrArg₂ (· * ·) ?_ (e2.trans (Finset.sum_congr rfl fun y hy => ?_))
  · rw [← e1]
  · rw [hW _ ((hmem N'' _).2 ⟨y, hR.1 y hy, rfl⟩), hφ]
    rfl

end GlobalTheory.MomT.Move
