import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSum

noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting

section Sum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS`.
-/
private theorem exists_sum (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ), ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, g ∉ S → F g = 0) → ∫ g, F g ∂μ = ∑ x ∈ T, c x * F (r x) :=
  _root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS

end Sum

section Ops

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Simplify using `only [atW]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
private theorem atW_val (w v : InfinitePlace E) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    atW w X a b v = (if v = w then X else 1) a b := by
  simp only [atW]
  split_ifs <;> rfl

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]`.
-/
private theorem of_atW_mul (w w' v : InfinitePlace E) (X Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' Y)) a b v =
      ((if v = w then X else 1) * (if v = w' then Y else 1)) a b := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Use extensionality with `a b v`. Rewrite using `[of_atW_mul]`. Distinguish the cases in `hv : v = w`. Simplify using `only [if_pos hv, h] show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v`. Simplify using `only [Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> rfl`. Simplify using `only [if_neg hv, mul_one] show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v`. Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
private theorem of_atW_inv (w : InfinitePlace E) {X Y : Matrix (Fin n) (Fin n) ℂ} (h : X * Y = 1) :
    (Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w Y) = 1 := by
  ext a b v
  rw [of_atW_mul]
  by_cases hv : v = w
  · simp only [if_pos hv, h]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · simp only [if_neg hv, mul_one]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

private def yAt (w : InfinitePlace E) (k : Un n) : GL (Fin n) (Cinf E) where
  val := Matrix.of (atW w k.1)
  inv := Matrix.of (atW w (star k.1))
  val_inv := of_atW_inv w (Unitary.mul_star_self_of_mem k.2)
  inv_val := of_atW_inv w (Unitary.star_mul_self_of_mem k.2)

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b v`. Use `show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v = ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v`. Rewrite using `[of_atW_mul, of_atW_mul]`. Distinguish the cases in `h1 : v = w`.

Establish `h2 : v ≠ w'` using `h1 ▸ h`. Simplify using `[h1, h]`. Simplify using `[h1]`.
-/
private theorem yAt_comm {w w' : InfinitePlace E} (h : w ≠ w') (k k' : Un n) : yAt w k * yAt w' k' = yAt w' k' * yAt w k := by
  apply Units.ext
  ext a b v
  show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v =
    ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v
  rw [of_atW_mul, of_atW_mul]
  by_cases h1 : v = w
  · have h2 : v ≠ w' := h1 ▸ h
    simp [h1, h]
  · simp [h1]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem coord_atW {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (X : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : coord τ (atW w X a b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `e` using `GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b`. Establish `c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q` using `coord_atW h k.1`. Establish `c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q` using `coord_atW h (star k.1)`. Simplify using `only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e`. Conclude with `e.symm`.
-/
private theorem commute_rt_Eop {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (k : Un n) (a b : Fin n) :
    Commute (Eop τ a b) (rt E n (infGL E n (yAt w k))) := by
  have e := GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b
  have c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q := coord_atW h k.1
  have c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q :=
    coord_atW h (star k.1)
  simp only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  exact e.symm

/- English proof (translation)
Establish `hl : ∀ x, Commute (lieS E n a b x) (finRep E n g)` using `fun x => by`. Rewrite using `[lieS_apply]`. Conclude with `lie_rt_fin _ g`. Establish `e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I))`. Rewrite using `[lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]`.

Use `module`. Rewrite using `[e]`. Conclude with `((hl _).sub_left ((hl _).smul_left _)).smul_left _`.
-/
private theorem commute_Eop_fin (τ : E →+* ℂ) (a b : Fin n) (g : GL (Fin n) (Af E)) :
    Commute (Eop τ a b) (finRep E n g) := by
  have hl : ∀ x, Commute (lieS E n a b x) (finRep E n g) := fun x => by
    rw [lieS_apply]
    exact lie_rt_fin _ g
  have e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I)) := by
    rw [lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact ((hl _).sub_left ((hl _).smul_left _)).smul_left _

/- English proof (translation)
Use `show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)`. Rewrite using `[← map_mul, ← map_mul, infGL_comm]`.
-/
private theorem commute_rt_fin (y : GL (Fin n) (Cinf E)) (g : GL (Fin n) (Af E)) :
    Commute (rt E n (infGL E n y)) (finRep E n g) := by
  show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)
  rw [← map_mul, ← map_mul, infGL_comm]

/- English proof (translation)
Take `⟨T, r, c, H⟩` from `exists_sum μf K hKo hKc hh.1`. Use `⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩` and prove the remaining obligations. Conclude with `Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _`. Use function extensionality and compare the values at `x`. Establish `e` using `H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)`.

Use `e.trans ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression.

Establish `e1 : h (g * k) = h g` using `by simpa using hh.2 1 K.one_mem k hk g`. Establish `e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g)` using `congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)`. Simplify using `only [e1, map_mul, ← mul_assoc, e2]`. Simplify using `[image_eq_zero_of_notMem_tsupport hg]`.
-/
private theorem exists_op [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (K : Subgroup (GL (Fin n) (Af E)))
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧
      ∀ ψ : Sm E n, (∀ k ∈ K, finRep E n k ψ = ψ) → heckeOp μf h ψ.1 = (A ψ).1 := by
  obtain ⟨T, r, c, H⟩ := exists_sum μf K hKo hKc hh.1
  refine ⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩
  · exact Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _
  · funext x
    have e := H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)
    · refine e.trans ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc]
      rfl
    · have e1 : h (g * k) = h g := by simpa using hh.2 1 K.one_mem k hk g
      have e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g) :=
        congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)
      simp only [e1, map_mul, ← mul_assoc, e2]
    · simp [image_eq_zero_of_notMem_tsupport hg]

end Ops

/- English proof (translation)
Introduce `E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D`. Set `ι : D.U →ₗ[ℂ] Sm E n` to `π.V.subtype ∘ₗ D.i`. Establish `hinj : Function.Injective ι` using `π.V.injective_subtype.comp D.inj`. Establish `lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) → (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B` using `fun A B A' B' hA hB hc => LinearMap.ext fun u => hinj <| by`. Use `LinearMap.congr_fun hc.eq (ι u)` as an intermediate fact.

Simplify using `only [Module.End.mul_apply] at this ⊢`. Rewrite using `[hA, hB, hB, hA, this]`. Establish `h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u)` using `fun w a b u => D.hE1 w a b u`. Establish `h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u)` using `fun w a b u => D.hE2 w a b u`. Establish `h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u)` using `fun w k u => Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))`.

Establish `h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u)` using `fun h => by`. Take `⟨A, hA, hA'⟩` from `exists_op μf K hKo hKc h.2`. Conclude with `⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩`. Establish `mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w` using `InfinitePlace.mk_embedding`. Establish `mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w` using `fun w => by`.

Rewrite using `[InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`. Establish `ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ'` using `fun h e => h (e ▸ rfl)`. Use `⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩` and prove the remaining obligations. Conclude with `lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)`. Conclude with `lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))`.

Conclude with `lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))`. Conclude with `lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)`. Conclude with `lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))`. Use `(lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]`.

Take `⟨A, hA, hA'⟩` from `h4 h`. Conclude with `lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)`. Take `⟨A, hA, hA'⟩` from `h4 h`. Conclude with `lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))`. Take `⟨A, hA, hA'⟩` from `h4 h`.

Conclude with `lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)`.
-/
theorem rlComm : RlComm := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hinj : Function.Injective ι := π.V.injective_subtype.comp D.inj
  have lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) →
      (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B := fun A B A' B' hA hB hc =>
    LinearMap.ext fun u => hinj <| by
      have := LinearMap.congr_fun hc.eq (ι u)
      simp only [Module.End.mul_apply] at this ⊢
      rw [hA, hB, hB, hA, this]
  have h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u) := fun w a b u => D.hE1 w a b u
  have h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u) :=
    fun w a b u => D.hE2 w a b u
  have h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u) := fun w k u =>
    Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))
  have h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n),
      (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u) := fun h => by
    obtain ⟨A, hA, hA'⟩ := exists_op μf K hKo hKc h.2
    exact ⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩
  have mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding
  have mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w := fun w => by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ' := fun h e => h (e ▸ rfl)
  refine ⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩
  · exact lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)
  · exact lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))
  · exact lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))
  · exact lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)
  · exact lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))
  · refine (lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq
    show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)

end UpperTheory.V.Z.GSp4Splitting
