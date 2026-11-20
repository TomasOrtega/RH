import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

/- English proof (translation)
Take `⟨a, ha, ha_uniq⟩` from `hfull (tvOf hw)`. Take `⟨α, hα, -, -⟩` from `exists_sepElt c.F.val.toRingHom (fun τ => embK c τ) (fun τ a => rfl)`. Take `⟨mm, hmm_def⟩ : ∃ mm : (E →+* ℂ) → TanM x Xo.univ.t.G, mm = fun τ' => ∑ i, a ⟨τ', i⟩ • tvOf (hu τ' i)` from `⟨_, rfl⟩`. Take `⟨mm', hmm'_def⟩ : ∃ mm' : (E →+* ℂ) → TanM x Xo.univ.t.G, mm' = fun τ' => if τ' = τ then tvOf hw else 0` from `⟨_, rfl⟩`. Establish `hmm : ∀ τ', IsEigV (actR (x0` using `x) (S := S) Xo.univ.t.act) (embK c τ') (mm τ') := by`.

Introduce `τ'`. Rewrite using `[hmm_def]`. Conclude with `eig_comb τ' (fun i => tvOf (hu τ' i)) (fun i => (eigAt_iff (c := c) (hu τ' i) τ').1 (heig τ' i)) (fun i => a ⟨τ', i⟩)`. Establish `hmm' : ∀ τ', IsEigV (actR (x0` using `x) (S := S) Xo.univ.t.act) (embK c τ') (mm' τ') := by`. Introduce `τ'`.

Rewrite using `[hmm'_def]`. Use `show IsEigV _ _ (if τ' = τ then tvOf hw else 0)`. Distinguish the cases in `h : τ' = τ`. Rewrite using `[if_pos h, h]`. Conclude with `(eigAt_iff (c := c) hw τ).1 hwe`.

Rewrite using `[if_neg h] show ∀ b, _ = _`. Introduce `b`. Rewrite using `[map_zero, smul_zero]`. Establish `hsum : ∑ τ', mm τ' = tvOf hw`. Rewrite using `[hmm_def, ha, Fintype.sum_sigma]`.

Establish `hsum' : ∑ τ', mm' τ' = tvOf hw`. Rewrite using `[hmm'_def]`. Simplify using the standard rewrite rules. Establish `h1` using `proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α) hα mm hmm τ`. Establish `h2` using `proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α) hα mm' hmm' τ`.

Rewrite `h1` using `[hsum]`. Rewrite `h2` using `[hsum']`. Establish `key : tvOf hw = mm τ`. Rewrite using `[← h1, h2, hmm'_def]`. Simplify using the standard rewrite rules.

Use `⟨fun i => a ⟨τ, i⟩, (combAt_iff (u τ) (hu τ) _ hw).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key, hmm_def]`. Introduce `b hb`. Rewrite `hb` using `[combAt_iff (u τ) (hu τ) b hw]`. Set `a' : (Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) → S` to `fun k => if h : k.1 = τ then b (Fin.cast (congrArg Dw.mult h) k.2) else 0`.

Establish `ha' : tvOf hw = ∑ k, a' k • tvOf (hu k.1 k.2)`. Rewrite using `[hb, Fintype.sum_sigma, Finset.sum_eq_single τ]`. Simplify using `[a']`. Introduce `τ' _ hne`. Simplify using `[a', hne]`.

Simplify using the standard rewrite rules. Establish `hA` using `ha_uniq a' ha'`. Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun hA ⟨τ, i⟩`. Simplify `hi` using `[a']`.
-/
theorem eig_basis_of_full {x : Sp S ⟶ Xo.X} (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, IsTanAt x (u τ i)) (heig : ∀ τ i, IsEigAt c τ (u τ i))
    (hfull : ∀ m : TanM x Xo.univ.t.G, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S,
      m = ∑ k, a k • tvOf (hu k.1 k.2))
    (τ : E →+* ℂ) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (hwe : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w := by
  classical
  obtain ⟨a, ha, ha_uniq⟩ := hfull (tvOf hw)
  obtain ⟨α, hα, -, -⟩ := exists_sepElt c.F.val.toRingHom (fun τ => embK c τ)
    (fun τ a => rfl)
  obtain ⟨mm, hmm_def⟩ : ∃ mm : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm = fun τ' => ∑ i, a ⟨τ', i⟩ • tvOf (hu τ' i) := ⟨_, rfl⟩
  obtain ⟨mm', hmm'_def⟩ : ∃ mm' : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm' = fun τ' => if τ' = τ then tvOf hw else 0 := ⟨_, rfl⟩
  have hmm : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm τ') := by
    intro τ'
    rw [hmm_def]
    exact eig_comb τ' (fun i => tvOf (hu τ' i))
      (fun i => (eigAt_iff (c := c) (hu τ' i) τ').1 (heig τ' i)) (fun i => a ⟨τ', i⟩)
  have hmm' : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm' τ') := by
    intro τ'
    rw [hmm'_def]
    show IsEigV _ _ (if τ' = τ then tvOf hw else 0)
    by_cases h : τ' = τ
    · rw [if_pos h, h]
      exact (eigAt_iff (c := c) hw τ).1 hwe
    · rw [if_neg h]
      show ∀ b, _ = _
      intro b
      rw [map_zero, smul_zero]
  have hsum : ∑ τ', mm τ' = tvOf hw := by
    rw [hmm_def, ha, Fintype.sum_sigma]
  have hsum' : ∑ τ', mm' τ' = tvOf hw := by
    rw [hmm'_def]
    simp
  have h1 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm hmm τ
  have h2 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm' hmm' τ
  rw [hsum] at h1
  rw [hsum'] at h2
  have key : tvOf hw = mm τ := by
    rw [← h1, h2, hmm'_def]
    simp
  refine ⟨fun i => a ⟨τ, i⟩, (combAt_iff (u τ) (hu τ) _ hw).2 ?_, ?_⟩
  · rw [key, hmm_def]
  · intro b hb
    rw [combAt_iff (u τ) (hu τ) b hw] at hb
    let a' : (Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) → S := fun k =>
      if h : k.1 = τ then b (Fin.cast (congrArg Dw.mult h) k.2) else 0
    have ha' : tvOf hw = ∑ k, a' k • tvOf (hu k.1 k.2) := by
      rw [hb, Fintype.sum_sigma, Finset.sum_eq_single τ]
      · simp [a']
      · intro τ' _ hne
        simp [a', hne]
      · simp
    have hA := ha_uniq a' ha'
    funext i
    have hi := congrFun hA ⟨τ, i⟩
    simpa [a'] using hi

end ReciprocityTheory.ChartRestriction.G.PullbackSections
