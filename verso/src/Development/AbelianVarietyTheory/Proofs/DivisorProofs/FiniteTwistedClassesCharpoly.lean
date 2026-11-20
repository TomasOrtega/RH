import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.UnitsPowers
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ClsFin

/- English proof (translation)
Take `⟨F, hF, hsq⟩` from `hsq`. Set `r : A → A` to `fun f => if h : ∃ s, (f * s ^ 2) * τ (f * s ^ 2) = 1 then f * h.choose ^ 2 else 1`. Use `⟨Set.image2 (fun f e => r f * e) F {t : A | t ^ 2 = 1}, hF.image2 _ h2, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, s, rfl⟩` from `hsq t`. Establish `h : ∃ s, (f * s ^ 2) * τ (f * s ^ 2) = 1` using `⟨s, ht⟩`.

Establish `hr : r f = f * h.choose ^ 2` using `dif_pos h`. Establish `h0` using `h.choose_spec`. Use `set s₀ := h.choose`. Use `⟨r f * ((s * s₀⁻¹) * τ (s * s₀⁻¹)), Set.mem_image2_of_mem hf ?_, (s * s₀⁻¹)⁻¹, ?_⟩` and prove the remaining obligations. Establish `e : ((s * s₀⁻¹) * τ (s * s₀⁻¹)) ^ 2 = ((f * s ^ 2) * τ (f * s ^ 2)) * ((f * s₀ ^ 2) * τ (f * s₀ ^ 2))⁻¹`.

Simplify using `only [map_mul, map_pow, map_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_inv]`. Normalize the expressions using the abelian group laws. Use `show _ = 1`.

Rewrite using `[e, ht, h0, inv_one, mul_one]`. Rewrite using `[hr]`. Simplify using `only [map_mul, map_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_inv]`.

Normalize the expressions using the abelian group laws.
-/
theorem cocycle_finite_comm {A : Type} [CommGroup A] (hsq : ∃ F : Set A, F.Finite ∧ ∀ t, ∃ f ∈ F, ∃ s, t = f * s ^ 2)
    (h2 : {t : A | t ^ 2 = 1}.Finite) (τ : A →* A) :
    ∃ F : Set A, F.Finite ∧ ∀ t, t * τ t = 1 → ∃ f ∈ F, ∃ s, t = s⁻¹ * f * τ s := by
  obtain ⟨F, hF, hsq⟩ := hsq
  let r : A → A := fun f => if h : ∃ s, (f * s ^ 2) * τ (f * s ^ 2) = 1 then f * h.choose ^ 2 else 1
  refine ⟨Set.image2 (fun f e => r f * e) F {t : A | t ^ 2 = 1}, hF.image2 _ h2, fun t ht => ?_⟩
  obtain ⟨f, hf, s, rfl⟩ := hsq t
  have h : ∃ s, (f * s ^ 2) * τ (f * s ^ 2) = 1 := ⟨s, ht⟩
  have hr : r f = f * h.choose ^ 2 := dif_pos h
  have h0 := h.choose_spec
  set s₀ := h.choose
  refine ⟨r f * ((s * s₀⁻¹) * τ (s * s₀⁻¹)), Set.mem_image2_of_mem hf ?_, (s * s₀⁻¹)⁻¹, ?_⟩
  · have e : ((s * s₀⁻¹) * τ (s * s₀⁻¹)) ^ 2 =
        ((f * s ^ 2) * τ (f * s ^ 2)) * ((f * s₀ ^ 2) * τ (f * s₀ ^ 2))⁻¹ := by
      simp only [map_mul, map_pow, map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv]
      abel
    show _ = 1
    rw [e, ht, h0, inv_one, mul_one]
  · rw [hr]
    simp only [map_mul, map_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv]
    abel

variable {G : Type} [Group G]

def SqFin (T : Subgroup G) : Prop :=
  (∀ s t : T, s * t = t * s) ∧ (∃ F : Set T, F.Finite ∧ ∀ t, ∃ f ∈ F, ∃ s, t = f * s ^ 2) ∧ {t : T | t ^ 2 = 1}.Finite

/- English proof (translation)
Use `letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hT.1 }`. Take `⟨F, hF, h⟩` from `cocycle_finite_comm hT.2.1 hT.2.2 ((τ.comp T.subtype).codRestrict T fun t => hτ _ t.2)`. Use `⟨Subtype.val '' F, hF.image _, fun t ht h1 => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, s, e⟩` from `h ⟨t, ht⟩ (Subtype.ext h1)`. Conclude with `⟨f, ⟨f, hf, rfl⟩, s, s.2, congrArg Subtype.val e⟩`.
-/
theorem cocycle_finite {T : Subgroup G} (hT : SqFin T) (τ : G →* G) (hτ : ∀ t ∈ T, τ t ∈ T) :
    ∃ F : Set G, F.Finite ∧ ∀ t ∈ T, t * τ t = 1 → ∃ f ∈ F, ∃ s ∈ T, t = s⁻¹ * f * τ s := by
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hT.1 }
  obtain ⟨F, hF, h⟩ := cocycle_finite_comm hT.2.1 hT.2.2
    ((τ.comp T.subtype).codRestrict T fun t => hτ _ t.2)
  refine ⟨Subtype.val '' F, hF.image _, fun t ht h1 => ?_⟩
  obtain ⟨f, hf, s, e⟩ := h ⟨t, ht⟩ (Subtype.ext h1)
  exact ⟨f, ⟨f, hf, rfl⟩, s, s.2, congrArg Subtype.val e⟩

/- English proof (translation)
The claim follows from `Quot.out_eq c`.
-/
theorem mk_rep {θ : G →* G} (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := Quot.out_eq c

/- English proof (translation)
Use `Set.Subsingleton.finite fun a ha b hb => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `hP _ _ ha hb`. Rewrite using `[← mk_rep a, ← mk_rep b]`. Conclude with `Quot.sound ⟨g, by rw [hθ]; exact hg⟩`.
-/
theorem finite_of_id (θ : G →* G) (hθ : ∀ g, θ g = g) (P : G → Prop)
    (hP : ∀ a b, P a → P b → ∃ g, b = g⁻¹ * a * g) : {c : TwCl θ | P c.rep}.Finite := by
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  obtain ⟨g, hg⟩ := hP _ _ ha hb
  rw [← mk_rep a, ← mk_rep b]
  exact Quot.sound ⟨g, by rw [hθ]; exact hg⟩

/- English proof (translation)
Break down `Set.eq_empty_or_nonempty {c : TwCl θ | P (c.rep * θ c.rep)} with h | ⟨c₀, h₀⟩` into its components or cases. Rewrite using `[h]`. Conclude with `Set.finite_empty`. Use `replace h₀ : P (c₀.rep * θ c₀.rep) := h₀`. Generalize the expression as in `c₀.rep = y₀ at h₀`.

Take `⟨F, hF, hc⟩` from `cocycle_finite (hT _ h₀) ((MulAut.conj y₀).toMonoidHom.comp θ) (by`. Introduce `t ht`. Rewrite `ht`, the goal using `[Subgroup.mem_centralizer_singleton_iff]`. Use `congrArg θ ht` as an intermediate fact. Simplify using `only [map_mul, hθ] at this`.

Use `show y₀ * θ t * y₀⁻¹ * (y₀ * θ y₀) = y₀ * θ y₀ * (y₀ * θ t * y₀⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Use `(hF.image fun f => (Quot.mk _ (f * y₀) : TwCl θ)).subset fun (c : TwCl θ) hc' => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `hP _ _ hc' h₀`. Take `⟨y, hy⟩ : ∃ y, y = g⁻¹ * c.rep * θ g` from `⟨_, rfl⟩`.

Establish `hN : y * θ y = y₀ * θ y₀`. Rewrite using `[hg, hy]`. Simplify using `only [map_mul, map_inv, hθ]`. Use `group`. Establish `hN' : θ y * y = θ y₀ * y₀`.

Use `congrArg θ hN` as an intermediate fact. Simplify `this` using `only [map_mul, hθ]`. Take `⟨f, hf, s, -, e⟩` from `hc (y * y₀⁻¹) (by`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Combine the equalities or inequalities in the displayed calculation.

Use `show y * y₀⁻¹ * (y₀ * θ (y * y₀⁻¹) * y₀⁻¹) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_inv]`. Use `group`. Use `_ = 1 := by rw [hN]; group)`.

Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Establish `e' : y = s⁻¹ * (f * y₀) * θ s`. Establish `e2 : y * y₀⁻¹ = s⁻¹ * f * (y₀ * θ s * y₀⁻¹)` using `e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mk_rep c]`.

Conclude with `(Quot.sound ⟨s, e'⟩).trans (Quot.sound ⟨g, hy⟩).symm`.
-/
theorem finite_twisted (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (P : G → Prop)
    (hP : ∀ a b, P a → P b → ∃ g, b = g⁻¹ * a * g) (hT : ∀ a, P a → SqFin (Subgroup.centralizer {a})) :
    {c : TwCl θ | P (c.rep * θ c.rep)}.Finite := by
  rcases Set.eq_empty_or_nonempty {c : TwCl θ | P (c.rep * θ c.rep)} with h | ⟨c₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  replace h₀ : P (c₀.rep * θ c₀.rep) := h₀
  generalize c₀.rep = y₀ at h₀
  obtain ⟨F, hF, hc⟩ := cocycle_finite (hT _ h₀) ((MulAut.conj y₀).toMonoidHom.comp θ) (by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
    have := congrArg θ ht
    simp only [map_mul, hθ] at this
    show y₀ * θ t * y₀⁻¹ * (y₀ * θ y₀) = y₀ * θ y₀ * (y₀ * θ t * y₀⁻¹)
    calc y₀ * θ t * y₀⁻¹ * (y₀ * θ y₀) = y₀ * (θ t * (θ y₀ * y₀)) * y₀⁻¹ := by group
      _ = _ := by rw [this]; group)
  refine (hF.image fun f => (Quot.mk _ (f * y₀) : TwCl θ)).subset fun (c : TwCl θ) hc' => ?_
  obtain ⟨g, hg⟩ := hP _ _ hc' h₀
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ * c.rep * θ g := ⟨_, rfl⟩
  have hN : y * θ y = y₀ * θ y₀ := by
    rw [hg, hy]; simp only [map_mul, map_inv, hθ]; group
  have hN' : θ y * y = θ y₀ * y₀ := by
    have := congrArg θ hN
    simpa only [map_mul, hθ] using this
  obtain ⟨f, hf, s, -, e⟩ := hc (y * y₀⁻¹) (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * y₀⁻¹ * (y₀ * θ y₀) = y * (θ y₀ * y₀) * y₀⁻¹ := by group
      _ = (y * θ y) * (y * y₀⁻¹) := by rw [← hN']; group
      _ = _ := by rw [hN]) (by
    show y * y₀⁻¹ * (y₀ * θ (y * y₀⁻¹) * y₀⁻¹) = 1
    calc y * y₀⁻¹ * (y₀ * θ (y * y₀⁻¹) * y₀⁻¹) = (y * θ y) * (θ y₀)⁻¹ * y₀⁻¹ := by
          rw [map_mul, map_inv]; group
      _ = 1 := by rw [hN]; group)
  refine ⟨f, hf, ?_⟩
  have e' : y = s⁻¹ * (f * y₀) * θ s := by
    have e2 : y * y₀⁻¹ = s⁻¹ * f * (y₀ * θ s * y₀⁻¹) := e
    calc y = y * y₀⁻¹ * y₀ := by group
      _ = _ := by rw [e2]; group
  rw [← mk_rep c]
  exact (Quot.sound ⟨s, e'⟩).trans (Quot.sound ⟨g, hy⟩).symm

/- English proof (translation)
Break down `Set.eq_empty_or_nonempty {c : TwCl (MonoidHom.id U) | P c.rep.1} with h | ⟨c₀, h₀⟩` into its components or cases. Rewrite using `[h]`. Conclude with `Set.finite_empty`. Establish `hγ : θ c₀.rep.1 = c₀.rep.1` using `(hU _).1 c₀.rep.2`. Use `replace h₀ : P c₀.rep.1 := h₀`.

Generalize the expression as in `c₀.rep.1 = γ at h₀ hγ`. Take `⟨F, hF, hc⟩` from `cocycle_finite (hT _ h₀) θ (by`. Introduce `t ht`. Rewrite `ht`, the goal using `[Subgroup.mem_centralizer_singleton_iff]`. Use `congrArg θ ht` as an intermediate fact.

Simplify `this)` using `only [map_mul, hγ]`. Establish `key : ∀ c : TwCl (MonoidHom.id U), ∃ h : G, P c.rep.1 → h * (θ h)⁻¹ ∈ F ∧ c.rep.1 = h⁻¹ * γ * h`. Introduce `c`. Distinguish the cases in `hc' : P c.rep.1`. Use `swap`.

Conclude with `⟨1, fun h => absurd h hc'⟩`. Take `⟨g, hg⟩` from `hP _ _ h₀ hc'`. Establish `h1 : θ c.rep.1 = c.rep.1` using `(hU _).1 c.rep.2`. Rewrite `h1` using `[hg]`. Simplify using `only [map_mul, map_inv, hγ] at h1`.

Take `⟨f, hf, s, hs, e⟩` from `hc (g * (θ g)⁻¹) (by`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_inv, hθ]`. Use the proof step `group)`.

Rewrite `hs` using `[Subgroup.mem_centralizer_singleton_iff]`. Use `⟨s * g, fun _ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: s * g * (θ (s * g))⁻¹ = f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]` and apply the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Use `choose h hh using key`. Use `Set.Finite.of_finite_image (f := fun c => h c * (θ (h c))⁻¹) (hF.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `(hh c hc).1`.

Introduce `a ha b hb hab`. Establish `hab' : h a * (θ (h a))⁻¹ = h b * (θ (h b))⁻¹` using `hab`. Establish `hu : (h a)⁻¹ * h b ∈ U`. Rewrite using `[hU, map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mk_rep a, ← mk_rep b]`. Use `Quot.sound ⟨⟨_, hu⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show b.rep.1 = ((h a)⁻¹ * h b)⁻¹ * a.rep.1 * ((h a)⁻¹ * h b)`. Rewrite using `[(hh a ha).2, (hh b hb).2]`. Use `group`.
-/
theorem finite_fixed (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (U : Subgroup G) (hU : ∀ g, g ∈ U ↔ θ g = g) (P : G → Prop)
    (hP : ∀ a b, P a → P b → ∃ g, b = g⁻¹ * a * g) (hT : ∀ a, P a → SqFin (Subgroup.centralizer {a})) :
    {c : TwCl (MonoidHom.id U) | P c.rep.1}.Finite := by
  rcases Set.eq_empty_or_nonempty {c : TwCl (MonoidHom.id U) | P c.rep.1} with h | ⟨c₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  have hγ : θ c₀.rep.1 = c₀.rep.1 := (hU _).1 c₀.rep.2
  replace h₀ : P c₀.rep.1 := h₀
  generalize c₀.rep.1 = γ at h₀ hγ
  obtain ⟨F, hF, hc⟩ := cocycle_finite (hT _ h₀) θ (by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
    have := congrArg θ ht
    simpa only [map_mul, hγ] using this)
  have key : ∀ c : TwCl (MonoidHom.id U), ∃ h : G, P c.rep.1 → h * (θ h)⁻¹ ∈ F ∧ c.rep.1 = h⁻¹ * γ * h := by
    intro c
    by_cases hc' : P c.rep.1
    swap
    · exact ⟨1, fun h => absurd h hc'⟩
    obtain ⟨g, hg⟩ := hP _ _ h₀ hc'
    have h1 : θ c.rep.1 = c.rep.1 := (hU _).1 c.rep.2
    rw [hg] at h1
    simp only [map_mul, map_inv, hγ] at h1
    obtain ⟨f, hf, s, hs, e⟩ := hc (g * (θ g)⁻¹) (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * (θ g)⁻¹ * γ = g * ((θ g)⁻¹ * γ * θ g) * (θ g)⁻¹ := by group
        _ = _ := by rw [h1]; group) (by
      simp only [map_mul, map_inv, hθ]; group)
    rw [Subgroup.mem_centralizer_singleton_iff] at hs
    refine ⟨s * g, fun _ => ⟨?_, ?_⟩⟩
    · have : s * g * (θ (s * g))⁻¹ = f := by
        calc s * g * (θ (s * g))⁻¹ = s * (g * (θ g)⁻¹) * (θ s)⁻¹ := by rw [map_mul]; group
          _ = f := by rw [e]; group
      rwa [this]
    · calc c.rep.1 = g⁻¹ * s⁻¹ * (s * γ) * g := by rw [hg]; group
        _ = _ := by rw [hs]; group
  choose h hh using key
  refine Set.Finite.of_finite_image (f := fun c => h c * (θ (h c))⁻¹) (hF.subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact (hh c hc).1
  · intro a ha b hb hab
    have hab' : h a * (θ (h a))⁻¹ = h b * (θ (h b))⁻¹ := hab
    have hu : (h a)⁻¹ * h b ∈ U := by
      rw [hU, map_mul, map_inv]
      calc (θ (h a))⁻¹ * θ (h b) = (h a)⁻¹ * (h a * (θ (h a))⁻¹) * θ (h b) := by group
        _ = _ := by rw [hab']; group
    rw [← mk_rep a, ← mk_rep b]
    refine Quot.sound ⟨⟨_, hu⟩, Subtype.ext ?_⟩
    show b.rep.1 = ((h a)⁻¹ * h b)⁻¹ * a.rep.1 * ((h a)⁻¹ * h b)
    rw [(hh a ha).2, (hh b hb).2]; group

section Mat

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.UnitLemma.PairClass.exists_intertwine K (Fin n → K) (Fin n → K) (toLin' b.val) (toLin' a.val) (by rw [charpoly_toLin', ← h]; exact hs) (by rw [charpoly_toLin', charpoly_toLin', h])`. Set `g : GL (Fin n) K` to `⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, eq_inv_mul_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises.

Apply `toLin'.injective` to reduce the goal to its premises. Use `ext1 i`. Use `ext1`. Simplify `he (Pi.single i 1)` using `[g, toLin'_mul]`.
-/
theorem conj_of_charpoly (a b : GL (Fin n) K) (hs : a.val.charpoly.Separable) (h : a.val.charpoly = b.val.charpoly) :
    ∃ g, b = g⁻¹ * a * g := by
  obtain ⟨e, he⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K (Fin n → K) (Fin n → K) (toLin' b.val) (toLin' a.val)
    (by rw [charpoly_toLin', ← h]; exact hs) (by rw [charpoly_toLin', charpoly_toLin', h])
  let g : GL (Fin n) K := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨g, ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  apply toLin'.injective
  ext1 i
  ext1
  simpa [g, toLin'_mul] using he (Pi.single i 1)

/- English proof (translation)
Take `⟨e, he⟩` from `Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (toLin' a) (by rw [charpoly_toLin']; exact hs)`. Establish `key : ∀ (p : K[X]) (v : Fin n → K), aeval (toLin' a) p v = aeval a p *ᵥ v`. Introduce `p v`. Establish `h1` using `aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom a p`. Conclude with `LinearMap.congr_fun h1 v`.

Establish `hc : ∀ q : K[X], b * aeval a q = aeval a q * b` using `fun q => by`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]`. Consider the case `monomial k c`. Rewrite using `[aeval_monomial]`.

Conclude with `(Commute.mul_right (Algebra.commutes c b).symm (Commute.pow_right h.symm k)).eq`. Take `⟨p, hp⟩` from `he (b *ᵥ e)`. Use `⟨p, toLin'.injective (LinearMap.ext fun v => ?_)⟩` and prove the remaining obligations. Take `⟨q, rfl⟩` from `he v`. Rewrite `hp` using `[key]`.

Rewrite using `[key, toLin'_apply, toLin'_apply, mulVec_mulVec, hc, ← mulVec_mulVec, ← hp, mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem exists_aeval_of_comm (a b : Matrix (Fin n) (Fin n) K) (hs : a.charpoly.Separable) (h : a * b = b * a) :
    ∃ p : K[X], b = aeval a p := by
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (toLin' a) (by rw [charpoly_toLin']; exact hs)
  have key : ∀ (p : K[X]) (v : Fin n → K), aeval (toLin' a) p v = aeval a p *ᵥ v := by
    intro p v
    have h1 := aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom a p
    exact LinearMap.congr_fun h1 v
  have hc : ∀ q : K[X], b * aeval a q = aeval a q * b := fun q => by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
    | monomial k c =>
      rw [aeval_monomial]
      exact (Commute.mul_right (Algebra.commutes c b).symm (Commute.pow_right h.symm k)).eq
  obtain ⟨p, hp⟩ := he (b *ᵥ e)
  refine ⟨p, toLin'.injective (LinearMap.ext fun v => ?_)⟩
  obtain ⟨q, rfl⟩ := he v
  rw [key] at hp
  rw [key, toLin'_apply, toLin'_apply, mulVec_mulVec, hc, ← mulVec_mulVec, ← hp, mulVec_mulVec, mulVec_mulVec,
    ← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Set `S` to `Subalgebra.centralizer K {a.val}`. Establish `hcomm : ∀ x y : S, x * y = y * x` using `fun x y => by`. Take `⟨p, hp⟩` from `exists_aeval_of_comm a.val x.1 hs (x.2 _ rfl)`. Take `⟨q, hq⟩` from `exists_aeval_of_comm a.val y.1 hs (y.2 _ rfl)`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show x.1 * y.1 = y.1 * x.1`. Rewrite using `[hp, hq, ← map_mul, ← map_mul, mul_comm]`. Use `letI : CommRing S := { (inferInstance : Ring S) with mul_comm := hcomm }`. Establish `h1` using `GlobalTheory.units_modSq_finite_of_fields K hK S`. Establish `h2` using `GlobalTheory.finite_sq_eq_one_of_finite_algebra K S`.

Set `j : Sˣ →* Subgroup.centralizer {a}` to `(Units.map S.val.toRingHom.toMonoidHom).codRestrict _ fun u => by`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `Units.ext (u.1.2 _ rfl).symm`. Establish `hinj : Function.Injective j` using `fun u v h => Units.ext (Subtype.ext (congrArg (fun x : Subgroup.centralizer {a} => x.1.val) h))`. Establish `hmem : ∀ t : Subgroup.centralizer {a}, t.1.val ∈ S` using `fun t m hm => by`.

Take `rfl : m = a.val` from `hm`. Conclude with `congrArg Units.val (t.2 a rfl)`. Establish `hsurj : Function.Surjective j` using `fun t => ⟨⟨⟨_, hmem t⟩, ⟨_, hmem t⁻¹⟩, Subtype.ext t.1.mul_inv, Subtype.ext t.1.inv_mul⟩, Subtype.ext (Units.ext rfl)⟩`. Use `⟨fun s t => ?_, ⟨Set.range fun q : Sˣ ⧸ (powMonoidHom 2 : Sˣ →* Sˣ).range => j q.out, Set.finite_range _, fun t => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hsurj s`.

Take `⟨t, rfl⟩` from `hsurj t`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Take `⟨t, rfl⟩` from `hsurj t`. Take `⟨⟨_, s, rfl⟩, hs⟩` from `QuotientGroup.mk_out_eq_mul (powMonoidHom 2 : Sˣ →* Sˣ).range t`. Use `⟨_, ⟨QuotientGroup.mk t, rfl⟩, j s⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, ← map_mul]`. Use `congr 1`. Rewrite using `[hs]`. Simplify using the standard rewrite rules. Use `((h2.preimage (f := (Units.val : Sˣ → S)) Units.val_injective.injOn).image j).subset fun t ht => ?_` and prove the remaining obligations.

Take `⟨u, rfl⟩` from `hsurj t`. Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Establish `: u ^ 2 = 1` using `hinj (by rw [map_pow, map_one]; exact ht)`. Use `show (u : S) ^ 2 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, this, Units.val_one]`.
-/
theorem sqFin_centralizer [CharZero K]
    (hK : ∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range))
    (a : GL (Fin n) K) (hs : a.val.charpoly.Separable) : SqFin (Subgroup.centralizer {a}) := by
  let S := Subalgebra.centralizer K {a.val}
  have hcomm : ∀ x y : S, x * y = y * x := fun x y => by
    obtain ⟨p, hp⟩ := exists_aeval_of_comm a.val x.1 hs (x.2 _ rfl)
    obtain ⟨q, hq⟩ := exists_aeval_of_comm a.val y.1 hs (y.2 _ rfl)
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    rw [hp, hq, ← map_mul, ← map_mul, mul_comm]
  letI : CommRing S := { (inferInstance : Ring S) with mul_comm := hcomm }
  have h1 := GlobalTheory.units_modSq_finite_of_fields K hK S
  have h2 := GlobalTheory.finite_sq_eq_one_of_finite_algebra K S
  let j : Sˣ →* Subgroup.centralizer {a} := (Units.map S.val.toRingHom.toMonoidHom).codRestrict _ fun u => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Units.ext (u.1.2 _ rfl).symm
  have hinj : Function.Injective j := fun u v h =>
    Units.ext (Subtype.ext (congrArg (fun x : Subgroup.centralizer {a} => x.1.val) h))
  have hmem : ∀ t : Subgroup.centralizer {a}, t.1.val ∈ S := fun t m hm => by
    obtain rfl : m = a.val := hm
    exact congrArg Units.val (t.2 a rfl)
  have hsurj : Function.Surjective j := fun t =>
    ⟨⟨⟨_, hmem t⟩, ⟨_, hmem t⁻¹⟩, Subtype.ext t.1.mul_inv, Subtype.ext t.1.inv_mul⟩, Subtype.ext (Units.ext rfl)⟩
  refine ⟨fun s t => ?_, ⟨Set.range fun q : Sˣ ⧸ (powMonoidHom 2 : Sˣ →* Sˣ).range => j q.out, Set.finite_range _,
    fun t => ?_⟩, ?_⟩
  · obtain ⟨s, rfl⟩ := hsurj s
    obtain ⟨t, rfl⟩ := hsurj t
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨t, rfl⟩ := hsurj t
    obtain ⟨⟨_, s, rfl⟩, hs⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom 2 : Sˣ →* Sˣ).range t
    refine ⟨_, ⟨QuotientGroup.mk t, rfl⟩, j s⁻¹, ?_⟩
    rw [← map_pow, ← map_mul]
    congr 1
    rw [hs]
    simp
  · refine ((h2.preimage (f := (Units.val : Sˣ → S)) Units.val_injective.injOn).image j).subset fun t ht => ?_
    obtain ⟨u, rfl⟩ := hsurj t
    refine ⟨u, ?_, rfl⟩
    have : u ^ 2 = 1 := hinj (by rw [map_pow, map_one]; exact ht)
    show (u : S) ^ 2 = 1
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

end Mat

/- English proof (translation)
Unfold `cj`. Use `split_ifs with h`. Take `⟨h1, h2⟩` from `h.choose_spec`. Use `congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (h1.comp h1) continuous_id ?_) x` and prove the remaining obligations. Use function extensionality and compare the values at `y`.

Simplify using `only [Function.comp_apply, h2, id]`. Rewrite using `[IsCMField.complexConj_apply_apply]`. Both sides reduce to the same expression.
-/
theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x : w.adicCompletion E) :
    cj w (cj w x) = x := by
  unfold cj
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h.choose_spec
    refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (h1.comp h1) continuous_id ?_) x
    funext y
    simp only [Function.comp_apply, h2, id]
    rw [IsCMField.complexConj_apply_apply]
  · rfl

/- English proof (translation)
Take `⟨vrL, topL, hlocL, -⟩` from `GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension (w.adicCompletion E) L`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Use `haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap (w.adicCompletion E) L).injective`. Conclude with `GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero`.
-/
theorem units_mod_sq {E : Type} [Field E] [NumberField E] (w : Pl E) (L : Type) [Field L]
    [Algebra (w.adicCompletion E) L] [FiniteDimensional (w.adicCompletion E) L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  obtain ⟨vrL, topL, hlocL, -⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension (w.adicCompletion E) L
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap (w.adicCompletion E) L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

/- English proof (translation)
Introduce `E _ _ _ _ n w Q hQ`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `hP : ∀ a b : GLw n w, a.val.charpoly = Q → b.val.charpoly = Q → ∃ g, b = g⁻¹ * a * g` using `fun a b ha hb => conj_of_charpoly a b (ha ▸ hQ) (ha.trans hb.symm)`. Establish `hT : ∀ a : GLw n w, a.val.charpoly = Q → SqFin (Subgroup.centralizer {a})` using `fun a ha => sqFin_centralizer (units_mod_sq w) a (ha ▸ hQ)`. Distinguish the cases in `hw : IsSplitAt w`.

Prove the components needed by the constructor for the conclusion. Simplify using `only [nrmL, if_pos hw]`. Conclude with `finite_of_id _ (fun g => by rw [thL, if_pos hw]; rfl) _ hP`. Conclude with `finite_fixed (MonoidHom.id _) (fun _ => rfl) _ (fun g => by rw [UL, if_pos hw]; simp) _ hP hT`. Establish `hth : thL n w = thetaGL n (cj w)` using `if_neg hw`.

Prove the components needed by the constructor for the conclusion. Establish `hn : ∀ y, nrmL n w y = y * thL n w y` using `fun y => by rw [nrmL, if_neg hw, hth]`. Simplify using `only [hn]`. Conclude with `finite_twisted _ (fun g => by rw [hth]; exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g) _ hP hT`. Use `finite_fixed ((invT n _).comp (GeneralLinearGroup.map (cj w))) (fun g => ?_) _ (fun g => ?_) _ hP hT` and prove the remaining obligations.

Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `cj_cj w _`. Rewrite using `[UL, if_neg hw]`. Express the relevant statement in the definitionally equal form `cT (cj w) g.val * 1 * g.val = 1 ↔ invT n _ (GeneralLinearGroup.map (cj w) g) = g`. Rewrite using `[mul_one, ← _root_.inv_inj (a := invT n _ _), ← mul_eq_one_iff_eq_inv, Units.ext_iff]`.

Both sides reduce to the same expression.
-/
theorem classes_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X]), Q.Separable → {c : TwCl (thL n w) | (nrmL n w c.rep).val.charpoly = Q}.Finite ∧ {c : TwCl (MonoidHom.id (UL n w)) | c.rep.1.val.charpoly = Q}.Finite := by
  intro E _ _ _ _ n w Q hQ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hP : ∀ a b : GLw n w, a.val.charpoly = Q → b.val.charpoly = Q → ∃ g, b = g⁻¹ * a * g :=
    fun a b ha hb => conj_of_charpoly a b (ha ▸ hQ) (ha.trans hb.symm)
  have hT : ∀ a : GLw n w, a.val.charpoly = Q → SqFin (Subgroup.centralizer {a}) :=
    fun a ha => sqFin_centralizer (units_mod_sq w) a (ha ▸ hQ)
  by_cases hw : IsSplitAt w
  · constructor
    · simp only [nrmL, if_pos hw]
      exact finite_of_id _ (fun g => by rw [thL, if_pos hw]; rfl) _ hP
    · exact finite_fixed (MonoidHom.id _) (fun _ => rfl) _ (fun g => by rw [UL, if_pos hw]; simp) _ hP hT
  · have hth : thL n w = thetaGL n (cj w) := if_neg hw
    constructor
    · have hn : ∀ y, nrmL n w y = y * thL n w y := fun y => by rw [nrmL, if_neg hw, hth]
      simp only [hn]
      exact finite_twisted _ (fun g => by rw [hth]; exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g) _ hP hT
    · refine finite_fixed ((invT n _).comp (GeneralLinearGroup.map (cj w))) (fun g => ?_) _ (fun g => ?_) _ hP hT
      · refine Units.ext (Matrix.ext fun i j => ?_)
        exact cj_cj w _
      · rw [UL, if_neg hw]
        change cT (cj w) g.val * 1 * g.val = 1 ↔ invT n _ (GeneralLinearGroup.map (cj w) g) = g
        rw [mul_one, ← _root_.inv_inj (a := invT n _ _), ← mul_eq_one_iff_eq_inv, Units.ext_iff]
        rfl

end GlobalTheory.BCT.ClsFin
