import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had`. Take `⟨-, -, h3, h4⟩` from `LevelTowerAlt.tor_facts A hΨ hv s`. Take `⟨h5, h6⟩` from `LevelTowerAlt.sub_eig A had.2`. Establish `h7` using `LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5`. Take `⟨e1, e2⟩` from `LevelTowerAlt.index_split A had.1 h3 h4 hq`.

Rewrite `h7` using `[LinPt.fam, e1]`. Establish `h8` using `(LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2`. Rewrite using `[LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LevelTowerAlt.label_degree_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had
  obtain ⟨-, -, h3, h4⟩ := LevelTowerAlt.tor_facts A hΨ hv s
  obtain ⟨h5, h6⟩ := LevelTowerAlt.sub_eig A had.2
  have h7 := LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5
  obtain ⟨e1, e2⟩ := LevelTowerAlt.index_split A had.1 h3 h4 hq
  rw [LinPt.fam, e1] at h7
  have h8 := (LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2
  rw [LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]
  ring
