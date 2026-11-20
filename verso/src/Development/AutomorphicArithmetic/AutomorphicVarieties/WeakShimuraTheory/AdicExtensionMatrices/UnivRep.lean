import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Unfold `IsGSp`. Rewrite using `[← Matrix.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Establish `h1 : (adj (X.map f) * X.map f) i j = f ((adj X * X) i j)`. Simplify using `only [Matrix.mul_apply, adj_apply, Matrix.map_apply, map_sum, map_mul, map_zsmul]`.

Establish `h2 : (f ν • (1 : M4 R')) i j = f ((ν • (1 : M4 R)) i j)`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1, h2, Matrix.sub_apply, map_sub, sub_eq_zero]`.
-/
private theorem gsp_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ν : R) (X : M4 R) :
    IsGSp (f ν) (X.map f) ↔ ∀ i j, f ((adj X * X - ν • (1 : M4 R)) i j) = 0 := by
  unfold IsGSp
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h1 : (adj (X.map f) * X.map f) i j = f ((adj X * X) i j) := by
    simp only [Matrix.mul_apply, adj_apply, Matrix.map_apply, map_sum, map_mul, map_zsmul]
  have h2 : (f ν • (1 : M4 R')) i j = f ((ν • (1 : M4 R)) i j) := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
    split_ifs <;> simp
  rw [h1, h2, Matrix.sub_apply, map_sub, sub_eq_zero]

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Establish `h2 : (1 : M4 R') i j = f ((1 : M4 R) i j)`. Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[h2, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]`.
-/
private theorem one_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) :
    X.map f = 1 ↔ ∀ i j, f ((X - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h2 : (1 : M4 R') i j = f ((1 : M4 R) i j) := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [h2, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]

/- English proof (translation)
Establish `e : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]`. Unfold `IsGSp`. Rewrite using `[e, Matrix.diagonal_mul_diagonal]`.

Use extensionality with `i j`. Simplify using `only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Use `split_ifs`. Rewrite using `[mul_comm, h, mul_one]`. Simplify using the standard rewrite rules.
-/
private theorem gsp_diag {R : Type} [CommRing R] (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) :
    IsGSp ν (Matrix.diagonal d) := by
  have e : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]
  unfold IsGSp
  rw [e, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_comm, h, mul_one]
  · simp

/- English proof (translation)
Introduce `R _ _ _ r`. Set `S : Set R` to `{x | (∃ g i j, (adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j = x) ∨ (∃ g ∈ Φ.N, ∃ i j, (r.hom g - 1) i j = x) ∨ ∃ i j, i ≠ j ∧ r.hom Φ.g0 i j = x}`. Use `⟨Ideal.span S, fun R' _ _ _ f => ?_⟩` and prove the remaining obligations. Establish `hs : (∀ x ∈ Ideal.span S, f x = 0) ↔ ∀ x ∈ S, f x = 0` using `⟨fun h x hx => h x (Ideal.subset_span hx), fun h _ hx => (Ideal.span_le (I := RingHom.ker f)).2 (fun y hy => h y hy) hx⟩`. Establish `e1 : ∀ g, IsGSp (((algebraMap Λ R').comp a) (Φ.ν g)) ((r.map f).hom g) ↔ ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j) = 0` using `fun g => by`.

Use `gsp_map_iff (f : R →+* R') (algebraMap Λ R (a (Φ.ν g))) (r.hom g)` as an intermediate fact. Rewrite using `[RingHom.comp_apply, ← f.commutes]`. Conclude with `this`. Establish `e2 : ∀ g, (r.map f).hom g = 1 ↔ ∀ i j, f ((r.hom g - 1) i j) = 0` using `fun g => one_map_iff (f : R →+* R') (r.hom g)`. Rewrite using `[hs]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `H x (⟨g, i, j, rfl⟩ | ⟨g, hg, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)`. Conclude with `(e1 g).1 (H.mult g) i j`. Conclude with `(e2 g).1 (H.kill g hg) i j`. Conclude with `H.nrm hij`.

Introduce `H`. Conclude with `⟨fun g => (e1 g).2 fun i j => H _ (Or.inl ⟨g, i, j, rfl⟩), fun g hg => (e2 g).2 fun i j => H _ (Or.inr (Or.inl ⟨g, hg, i, j, rfl⟩)), fun i j hij => H _ (Or.inr (Or.inr ⟨i, j, hij, rfl⟩))⟩`.
-/
private theorem rep_closed {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ) (rbar : Γ →* M4 (ResidueField Λ)) :
    Cond.IsClosed (rbar := rbar) fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom := by
  intro R _ _ _ r
  let S : Set R := {x | (∃ g i j, (adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j = x) ∨
    (∃ g ∈ Φ.N, ∃ i j, (r.hom g - 1) i j = x) ∨ ∃ i j, i ≠ j ∧ r.hom Φ.g0 i j = x}
  refine ⟨Ideal.span S, fun R' _ _ _ f => ?_⟩
  have hs : (∀ x ∈ Ideal.span S, f x = 0) ↔ ∀ x ∈ S, f x = 0 :=
    ⟨fun h x hx => h x (Ideal.subset_span hx), fun h _ hx =>
      (Ideal.span_le (I := RingHom.ker f)).2 (fun y hy => h y hy) hx⟩
  have e1 : ∀ g, IsGSp (((algebraMap Λ R').comp a) (Φ.ν g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j) = 0 := fun g => by
    have := gsp_map_iff (f : R →+* R') (algebraMap Λ R (a (Φ.ν g))) (r.hom g)
    rw [RingHom.comp_apply, ← f.commutes]
    exact this
  have e2 : ∀ g, (r.map f).hom g = 1 ↔ ∀ i j, f ((r.hom g - 1) i j) = 0 := fun g =>
    one_map_iff (f : R →+* R') (r.hom g)
  rw [hs]
  constructor
  · rintro H x (⟨g, i, j, rfl⟩ | ⟨g, hg, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact (e1 g).1 (H.mult g) i j
    · exact (e2 g).1 (H.kill g hg) i j
    · exact H.nrm hij
  · intro H
    exact ⟨fun g => (e1 g).2 fun i j => H _ (Or.inl ⟨g, i, j, rfl⟩),
      fun g hg => (e2 g).2 fun i j => H _ (Or.inr (Or.inl ⟨g, hg, i, j, rfl⟩)),
      fun i j hij => H _ (Or.inr (Or.inr ⟨i, j, hij, rfl⟩))⟩

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a h`. Use `haveI := h.char`. Establish `hd : ∀ g, (Φ.splitRD ((residue Λ).comp a)).r g = Matrix.diagonal fun i => ((residue Λ).comp a) (Φ.χ i g)` using `fun g => by show (Matrix.diagonal fun i => (Φ.χ i g : O)).map ((residue Λ).comp a) = _`. Conclude with `Matrix.diagonal_map (map_zero _)`. Establish `hlc : IsLocallyConstant (Φ.splitRD ((residue Λ).comp a)).r`.

Establish `h4 : IsLocallyConstant fun g => fun i => ((residue Λ).comp a) (Φ.χ i g)`. Use `(((h.ok.lc 0).prodMk (h.ok.lc 1)).prodMk ((h.ok.lc 2).prodMk (h.ok.lc 3))).comp fun x => ![x.1.1, x.1.2, x.2.1, x.2.2]` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g i`. Apply the tactic sequence `fin_cases i <;> rfl`.

Use `h4.comp Matrix.diagonal` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `hd g`. Establish `hk : ∀ n ∈ Φ.N, (Φ.splitRD ((residue Λ).comp a)).r n = 1` using `fun n hn => by`.

Rewrite using `[hd]`. Simplify using `only [h.ok.kill n hn, Matrix.diagonal_one]`. Take `⟨R, _, _, _, r, hr⟩` from `sxUnivKill l (Φ.splitRD ((residue Λ).comp a)).r Φ.N h.phi hlc hk`. Use `haveI := (co_res Λ).1`. Set `r₁ : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r (ResidueField Λ)` to `{ hom := (Φ.splitRD ((residue Λ).comp a)).r cont := fun i j N => hlc.comp fun X => Ideal.Quotient.mk _ (X i j) red := fun g i j => by`.

Take `⟨x, hx⟩` from `residue_surjective ((Φ.splitRD ((residue Λ).comp a)).r g i j)`. Rewrite using `[← hx]`. Conclude with `(res Λ (ResidueField Λ)).commutes x }`. Establish `h1 : Φ.IsRep ((algebraMap Λ (ResidueField Λ)).comp a) r₁.hom`. Use `⟨fun g => ?_, hk, ?_⟩` and prove the remaining obligations.

Use `show IsGSp (((residue Λ).comp a) (Φ.ν g)) ((Φ.splitRD ((residue Λ).comp a)).r g)`. Rewrite using `[hd]`. Use `gsp_diag _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← Units.val_mul, h.ok.mul]`. Use `show ((Φ.splitRD ((residue Λ).comp a)).r Φ.g0).IsDiag`.

Rewrite using `[hd]`. Conclude with `Matrix.isDiag_diagonal _`. Take `⟨R', _, _, _, p, -, hp⟩` from `univ_cond Λ Γ (Fin 4) _ R r _ _ hr (rep_closed Φ a _) ⟨ResidueField Λ, inferInstance, inferInstance, inferInstance, r₁, hk, h1⟩`. Use `⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ => ⟨fun f => ((hp C).1 f).2, fun s hs => (hp C).2 s ⟨hs.kill, hs⟩⟩⟩` and prove the remaining obligations.
-/
theorem UpperTheory.V.Ws.sxUnivRep :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R), Represents (fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom) r := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a h
  haveI := h.char
  have hd : ∀ g, (Φ.splitRD ((residue Λ).comp a)).r g =
      Matrix.diagonal fun i => ((residue Λ).comp a) (Φ.χ i g) := fun g => by
    show (Matrix.diagonal fun i => (Φ.χ i g : O)).map ((residue Λ).comp a) = _
    exact Matrix.diagonal_map (map_zero _)
  have hlc : IsLocallyConstant (Φ.splitRD ((residue Λ).comp a)).r := by
    have h4 : IsLocallyConstant fun g => fun i => ((residue Λ).comp a) (Φ.χ i g) := by
      have := (((h.ok.lc 0).prodMk (h.ok.lc 1)).prodMk ((h.ok.lc 2).prodMk (h.ok.lc 3))).comp
        fun x => ![x.1.1, x.1.2, x.2.1, x.2.2]
      convert this using 1
      funext g i
      fin_cases i <;> rfl
    have := h4.comp Matrix.diagonal
    convert this using 1
    funext g
    exact hd g
  have hk : ∀ n ∈ Φ.N, (Φ.splitRD ((residue Λ).comp a)).r n = 1 := fun n hn => by
    rw [hd]
    simp only [h.ok.kill n hn, Matrix.diagonal_one]
  obtain ⟨R, _, _, _, r, hr⟩ := sxUnivKill l (Φ.splitRD ((residue Λ).comp a)).r Φ.N h.phi hlc hk
  haveI := (co_res Λ).1
  let r₁ : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r (ResidueField Λ) :=
    { hom := (Φ.splitRD ((residue Λ).comp a)).r
      cont := fun i j N => hlc.comp fun X => Ideal.Quotient.mk _ (X i j)
      red := fun g i j => by
        obtain ⟨x, hx⟩ := residue_surjective ((Φ.splitRD ((residue Λ).comp a)).r g i j)
        rw [← hx]
        exact (res Λ (ResidueField Λ)).commutes x }
  have h1 : Φ.IsRep ((algebraMap Λ (ResidueField Λ)).comp a) r₁.hom := by
    refine ⟨fun g => ?_, hk, ?_⟩
    · show IsGSp (((residue Λ).comp a) (Φ.ν g)) ((Φ.splitRD ((residue Λ).comp a)).r g)
      rw [hd]
      refine gsp_diag _ _ fun i => ?_
      rw [← map_mul, ← Units.val_mul, h.ok.mul]
    · show ((Φ.splitRD ((residue Λ).comp a)).r Φ.g0).IsDiag
      rw [hd]
      exact Matrix.isDiag_diagonal _
  obtain ⟨R', _, _, _, p, -, hp⟩ := univ_cond Λ Γ (Fin 4) _ R r _ _ hr (rep_closed Φ a _)
    ⟨ResidueField Λ, inferInstance, inferInstance, inferInstance, r₁, hk, h1⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((hp C).1 f).2, fun s hs => (hp C).2 s ⟨hs.kill, hs⟩⟩⟩
