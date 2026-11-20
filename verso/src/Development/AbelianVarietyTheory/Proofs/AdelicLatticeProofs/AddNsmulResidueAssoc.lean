import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinMod

open GlobalTheory.LatVac

/- English proof (translation)
Proceed by induction on `G, hG using Set.Finite.induction_on with`. Consider the case `empty => exact ⟨{0}, Set.finite_singleton _, fun x hx => ⟨0, rfl, 0, zero_mem _, by simpa using hx⟩⟩`. Consider the case `@insert g G _ _ ih`. Take `⟨R, hR, h⟩` from `ih`. Use `⟨Set.image2 (fun (j : ℤ) r => j • g + r) (Set.Ico 0 k) R, (Set.finite_Ico _ _).image2 _ hR, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨c, y, hy, rfl⟩` from `Submodule.mem_span_insert.1 hx`. Take `⟨r, hr, u, hu, rfl⟩` from `h y hy`. Establish `hk' : (0 : ℤ) < k` using `by exact_mod_cast hk`. Use `⟨_, ⟨c % k, ⟨Int.emod_nonneg _ hk'.ne', Int.emod_lt_of_pos _ hk'⟩, r, hr, rfl⟩, (c / k) • g + u, Submodule.mem_span_insert.2 ⟨_, u, hu, rfl⟩, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Int.emod_add_mul_ediv c k]`.

Simplify using `only [add_smul, mul_smul, smul_add, natCast_zsmul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_finite_mod {W : Type} [AddCommGroup W] {G : Set W} (hG : G.Finite) {k : ℕ} (hk : 0 < k) :
    ∃ R : Set W, R.Finite ∧ ∀ x ∈ Submodule.span ℤ G, ∃ r ∈ R, ∃ u ∈ Submodule.span ℤ G, x = r + k • u := by
  induction G, hG using Set.Finite.induction_on with
  | empty => exact ⟨{0}, Set.finite_singleton _, fun x hx => ⟨0, rfl, 0, zero_mem _, by simpa using hx⟩⟩
  | @insert g G _ _ ih =>
    obtain ⟨R, hR, h⟩ := ih
    refine ⟨Set.image2 (fun (j : ℤ) r => j • g + r) (Set.Ico 0 k) R, (Set.finite_Ico _ _).image2 _ hR,
      fun x hx => ?_⟩
    obtain ⟨c, y, hy, rfl⟩ := Submodule.mem_span_insert.1 hx
    obtain ⟨r, hr, u, hu, rfl⟩ := h y hy
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    refine ⟨_, ⟨c % k, ⟨Int.emod_nonneg _ hk'.ne', Int.emod_lt_of_pos _ hk'⟩, r, hr, rfl⟩,
      (c / k) • g + u, Submodule.mem_span_insert.2 ⟨_, u, hu, rfl⟩, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv c k]
    simp only [add_smul, mul_smul, smul_add, natCast_zsmul]
    abel

/- English proof (translation)
Establish `h1 : Module.Finite (𝓞 E) N` using `Module.Finite.iff_fg.2 hN`. Establish `h2 : Module.Finite ℤ N` using `Module.Finite.trans (𝓞 E) N`. Take `⟨s, hs⟩` from `h2.fg_top`. Use `⟨Subtype.val '' (s : Set N), s.finite_toSet.image _, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, -, rfl⟩`.

Conclude with `y.2`. Establish `: (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (s : Set N)` using `by rw [hs]; trivial`. Conclude with `Submodule.apply_mem_span_image_of_mem_span (N.subtype.toAddMonoidHom.toIntLinearMap) this`.
-/
theorem exists_int_gen {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module (𝓞 E) M]
    (N : Submodule (𝓞 E) M) (hN : N.FG) :
    ∃ A : Set M, A.Finite ∧ A ⊆ N ∧ ∀ x ∈ N, x ∈ Submodule.span ℤ A := by
  have h1 : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have h2 : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨s, hs⟩ := h2.fg_top
  refine ⟨Subtype.val '' (s : Set N), s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · have : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (s : Set N) := by rw [hs]; trivial
    exact Submodule.apply_mem_span_image_of_mem_span (N.subtype.toAddMonoidHom.toIntLinearMap) this

/- English proof (translation)
Establish `gen : ∀ {U : Type} [AddCommGroup U] (g : U → W), (∀ u u', g (u + u') = g u + g u') → ∀ (N : Submodule ℤ W) (V : Set U), (∀ u ∈ V, g u ∈ N) → ∀ u ∈ Submodule.span ℤ V, g u ∈ N`. Introduce `U _ g hg N V hV u hu`. Establish `: Submodule.span ℤ V ≤ N.comap (AddMonoidHom.mk' g hg).toIntLinearMap` using `Submodule.span_le.2 hV`. Conclude with `this hu`. Use `gen (fun a => f a s t) (fun a a' => h1 a a' s t) _ A (fun a ha => ?_) a ha` and prove the remaining obligations.

Use `gen (fun s => f a s t) (fun s s' => h2 a s s' t) _ B (fun s hs => ?_) s hs` and prove the remaining obligations. Use `gen (fun t => f a s t) (h3 a s) _ C (fun t ht => ?_) t ht` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨(a, s, t), ⟨ha, hs, ht⟩, rfl⟩`.
-/
theorem triadd_mem_span {X Y Z W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    (f : X → Y → Z → W) (h1 : ∀ a a' s t, f (a + a') s t = f a s t + f a' s t)
    (h2 : ∀ a s s' t, f a (s + s') t = f a s t + f a s' t) (h3 : ∀ a s t t', f a s (t + t') = f a s t + f a s t')
    {A : Set X} {B : Set Y} {C : Set Z} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    f a s t ∈ Submodule.span ℤ ((fun p : X × Y × Z => f p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  have gen : ∀ {U : Type} [AddCommGroup U] (g : U → W), (∀ u u', g (u + u') = g u + g u') →
      ∀ (N : Submodule ℤ W) (V : Set U), (∀ u ∈ V, g u ∈ N) → ∀ u ∈ Submodule.span ℤ V, g u ∈ N := by
    intro U _ g hg N V hV u hu
    have : Submodule.span ℤ V ≤ N.comap (AddMonoidHom.mk' g hg).toIntLinearMap := Submodule.span_le.2 hV
    exact this hu
  refine gen (fun a => f a s t) (fun a a' => h1 a a' s t) _ A (fun a ha => ?_) a ha
  refine gen (fun s => f a s t) (fun s s' => h2 a s s' t) _ B (fun s hs => ?_) s hs
  refine gen (fun t => f a s t) (h3 a s) _ C (fun t ht => ?_) t ht
  exact Submodule.subset_span ⟨(a, s, t), ⟨ha, hs, ht⟩, rfl⟩

/- English proof (translation)
Simplify using `[mul_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem star_sum_add {E : Type} [CommRing E] [StarRing E] {n : ℕ} (c : E) (s s' g : Fin n → E) :
    c * ∑ k, star ((s + s') k) * g k = c * ∑ k, star (s k) * g k + c * ∑ k, star (s' k) * g k := by
  simp [mul_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hp : pairA F 0 (ε * (algebraMap F _ x + k • β)) = x • pairA F 0 ε + k • pairA F 0 (ε * β)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf F) = x • 0 + k • 0`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `ε * (algebraMap F _ x + k • β) = x • ε + k • (ε * β)`.

Rewrite using `[mul_add, mul_smul_comm, Algebra.smul_def x, mul_comm ε]`. Rewrite using `[hp, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def x, ← mul_assoc, ← mul_assoc]`.
-/
theorem pair_tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (ε β : Af F) (x : F) (k : ℕ) (a t g : E) :
    pairA F 0 (ε * (algebraMap F _ x + k • β)) ⊗ₜ[F] (a * t * g) =
      pairA F 0 ε ⊗ₜ[F] (algebraMap F E x * a * t * g) + k • (pairA F 0 (ε * β) ⊗ₜ[F] (a * t * g)) := by
  have hp : pairA F 0 (ε * (algebraMap F _ x + k • β)) = x • pairA F 0 ε + k • pairA F 0 (ε * β) := by
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = x • 0 + k • 0
      simp
    · change ε * (algebraMap F _ x + k • β) = x • ε + k • (ε * β)
      rw [mul_add, mul_smul_comm, Algebra.smul_def x, mul_comm ε]
  rw [hp, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def x,
    ← mul_assoc, ← mul_assoc]

/- English proof (translation)
Rewrite using `[smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem add_nsmul_residue_add {W : Type} [AddCommGroup W] (k : ℕ) (y u y' u' : W) :
    y + k • u + (y' + k • u') = y + y' + k • (u + u') := by rw [smul_add]; abel

/- English proof (translation)
Rewrite using `[smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem neg_nsmul_residue {W : Type} [AddCommGroup W] (k : ℕ) (y u : W) : -(y + k • u) = -y + k • -u := by
  rw [smul_neg]; abel

/- English proof (translation)
Rewrite using `[smul_add, add_assoc]`.
-/
theorem add_nsmul_residue_assoc {W : Type} [AddCommGroup W] (k : ℕ) (r u' u : W) :
    r + k • u' + k • u = r + k • (u' + u) := by rw [smul_add, add_assoc]

variable {D : D7}

/- English proof (translation)
Use `triadd_mem_span (genMap S T) (fun a a' s t => ?_) (fun a s s' t => ?_) (fun a s t t' => ?_) ha hs ht` and prove the remaining obligations. Conclude with `Matrix.ext fun i j => (congrArg (· * _) (add_mul a a' (t i))).trans (add_mul _ _ _)`. Conclude with `Matrix.ext fun i j => star_sum_add (a * t i) s s' fun k => S.gram k j`. Conclude with `Matrix.ext fun i j => (congrArg (· * _) (mul_add a (t i) (t' i))).trans (add_mul _ _ _)`.
-/
theorem genMap_mem_span (S T : HSp D) {A : Set D.host.E} {B : Set (Fin S.rank → D.host.E)}
    {C : Set (Fin T.rank → D.host.E)} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    genMap S T a s t ∈ Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  refine triadd_mem_span (genMap S T) (fun a a' s t => ?_) (fun a s s' t => ?_) (fun a s t t' => ?_) ha hs ht
  · exact Matrix.ext fun i j => (congrArg (· * _) (add_mul a a' (t i))).trans (add_mul _ _ _)
  · exact Matrix.ext fun i j => star_sum_add (a * t i) s s' fun k => S.gram k j
  · exact Matrix.ext fun i j => (congrArg (· * _) (mul_add a (t i) (t' i))).trans (add_mul _ _ _)

open Classical in

def idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop)
    (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemAt F P) = if P v then 1 else 0 := rfl

/- English proof (translation)
Introduce `D S T ΛS ΛT hS hT P k hk`. Take `⟨A, hA, hA1, hA2⟩` from `exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)`. Take `⟨B, hB, hB1, hB2⟩` from `exists_int_gen ΛS hS`. Take `⟨C, hC, hC1, hC2⟩` from `exists_int_gen ΛT hT`. Set `ε` to `idemAt D.host.F P`.

Establish `hε : ε ∈ intAf D.host.F`. Introduce `v`. Rewrite using `[evalV_idemAt]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0` using `fun v hv => by rw [evalV_idemAt, if_neg hv]`. Set `φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T` to `(AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap`. Set `G` to `φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))`. Establish `hG : G.Finite` using `((hA.prod (hB.prod hC)).image _).image _`.

Use `set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P`. Establish `hGΛ : ∀ x ∈ Submodule.span ℤ G, x ∈ Λ`. Establish `: Submodule.span ℤ G ≤ Λ.toIntSubmodule`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩`.

Conclude with `AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩`. Conclude with `fun x hx => this hx`. Establish `key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u`. Introduce `w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`.

Consider the case `mem w hw`. Take `⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩` from `hw`. Take `⟨x, β, hβ, hx⟩` from `(GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα`. Establish `e : α = ε * α`. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `evalV D.host.F v α = evalV D.host.F v (ε * α)`. Rewrite using `[map_mul, evalV_idemAt]`. Use `split_ifs with hv`. Rewrite using `[one_mul]`. Rewrite using `[h0 v hv, mul_zero]`.

Establish `hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)` using `Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha`. Use `⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t), Submodule.apply_mem_span_image_of_mem_span φ (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)), finTens (ε * β) (genMap S T a s t), AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, …` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_mem (hε v) (hβ v)`. Rewrite using `[map_mul, hε0 v hv, zero_mul]`.

Rewrite using `[e, hx]`. Conclude with `Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _`. Consider the case `zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩`. Consider the case `add x x' _ _ h h'`. Take `⟨y, hy, u, hu, rfl⟩` from `h`.

Take `⟨y', hy', u', hu', rfl⟩` from `h'`. Conclude with `⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩`. Consider the case `neg x _ h`. Take `⟨y, hy, u, hu, rfl⟩` from `h`. Conclude with `⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩`.

Take `⟨R, hR, h⟩` from `exists_finite_mod hG hk`. Use `⟨R, hR, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, u, hu, rfl⟩` from `key w hw`. Take `⟨r, hr, u', hu', rfl⟩` from `h y hy`. Conclude with `⟨r, hr, u' + u, add_mem (hGΛ _ hu') hu, add_nsmul_residue_assoc k r u' u⟩`.
-/
theorem latO_finite_mod : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ΛS.FG → ΛT.FG → ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (k : ℕ), 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, ∃ r ∈ R, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, t = r + k • u := by
  intro D S T ΛS ΛT hS hT P k hk
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ Submodule.span ℤ G, x ∈ Λ := by
    have : Submodule.span ℤ G ≤ Λ.toIntSubmodule := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
      exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    exact fun x hx => this hx
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨R, hR, h⟩ := exists_finite_mod hG hk
  refine ⟨R, hR, fun w hw => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  obtain ⟨r, hr, u', hu', rfl⟩ := h y hy
  exact ⟨r, hr, u' + u, add_mem (hGΛ _ hu') hu, add_nsmul_residue_assoc k r u' u⟩

end GlobalTheory.LatFinMod

end
