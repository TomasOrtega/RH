import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CocW

/- English proof (translation)
Establish `: inclR (F` using `F) R e = (1 : R) ⊗ₜ[F] e := rfl`. Rewrite using `[this, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using the standard rewrite rules.
-/
theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R e) k = algebraMap F R (b.repr e k) := by
  have : inclR (F := F) R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

/- English proof (translation)
Take `⟨⟨hlc, hsc, ht2⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Take `⟨hC, hfin, hnc⟩` from `GlobalTheory.T.adele_ring_cocompact_discrete_number_field F`. Take `⟨-, -, -, -, -, -, hb, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hd : 0 < Module.finrank F E` using `by rw [h.2.2.1]; norm_num`.

Set `b` to `Module.finBasis F E`. Set `φ : AF F ⊗[F] E → Fin (Module.finrank F E) → AF F` to `fun y k => (Algebra.TensorProduct.basis (AF F) b).repr y k`. Establish `hφ : IsHomeomorph φ` using `hb _ b`. Establish `hcont : ∀ k, Continuous fun y => φ y k` using `fun k => (continuous_apply k).comp hφ.continuous`. Establish `hsub : ∀ y e k, φ (y - inclR (AF F) e) k = φ y k - algebraMap F (AF F) (b.repr e k)`.

Introduce `y e k`. Simplify using `only [φ, map_sub, Finsupp.sub_apply, repr_inclR]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨C, hCc, hCy⟩` from `hC`. Use `⟨φ ⁻¹' Set.pi Set.univ fun _ => C, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hφ.homeomorph φ).isCompact_preimage.2 (isCompact_univ_pi fun _ => hCc)`. Introduce `y choose l hl using fun k => hCy (φ y k)`. Use `⟨∑ k, l k • b k, ?_⟩` and prove the remaining obligations. Introduce `k _`. Rewrite using `[hsub, b.repr_sum_self]`.

Conclude with `hl k`. Introduce `C hCc`. Establish `hS : ∀ k, {l : F | algebraMap F (AF F) l ∈ (fun y => φ y k) '' C}.Finite` using `fun k => hfin _ (hCc.image (hcont k))`. Use `((Set.Finite.pi hS).preimage (f := fun (e : E) k => b.repr e k) ?_).subset ?_` and prove the remaining obligations. Introduce `x _ y _ hxy`.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Conclude with `congrFun hxy k`. Introduce `e he k _`. Use `⟨inclR (AF F) e, he, ?_⟩` and prove the remaining obligations.

Conclude with `repr_inclR (AF F) b e k`. Use `⟨fun hK => hnc.noncompact_univ ?_⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective fun y => φ y ⟨0, hd⟩`. Introduce `r`. Take `⟨y, hy⟩` from `hφ.surjective fun _ => r`.

Conclude with `⟨y, congrFun hy _⟩`. Use `hK.image (hcont ⟨0, hd⟩)` as an intermediate fact. Rewrite `this` using `[Set.image_univ, hsurj.range_eq]`. Then use the resulting hypothesis.
-/
theorem scalar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    (∃ C : Set (AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ e : E, y - inclR (AF F) e ∈ C) ∧
    (∀ C : Set (AF F ⊗[F] E), IsCompact C → {e : E | inclR (AF F) e ∈ C}.Finite) ∧
    NoncompactSpace (AF F ⊗[F] E) := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨hC, hfin, hnc⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hd : 0 < Module.finrank F E := by rw [h.2.2.1]; norm_num
  let b := Module.finBasis F E
  let φ : AF F ⊗[F] E → Fin (Module.finrank F E) → AF F :=
    fun y k => (Algebra.TensorProduct.basis (AF F) b).repr y k
  have hφ : IsHomeomorph φ := hb _ b
  have hcont : ∀ k, Continuous fun y => φ y k := fun k => (continuous_apply k).comp hφ.continuous
  have hsub : ∀ y e k, φ (y - inclR (AF F) e) k = φ y k - algebraMap F (AF F) (b.repr e k) := by
    intro y e k
    simp only [φ, map_sub, Finsupp.sub_apply, repr_inclR]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hCc, hCy⟩ := hC
    refine ⟨φ ⁻¹' Set.pi Set.univ fun _ => C, ?_, ?_⟩
    · exact (hφ.homeomorph φ).isCompact_preimage.2 (isCompact_univ_pi fun _ => hCc)
    · intro y
      choose l hl using fun k => hCy (φ y k)
      refine ⟨∑ k, l k • b k, ?_⟩
      intro k _
      rw [hsub, b.repr_sum_self]
      exact hl k
  · intro C hCc
    have hS : ∀ k, {l : F | algebraMap F (AF F) l ∈ (fun y => φ y k) '' C}.Finite :=
      fun k => hfin _ (hCc.image (hcont k))
    refine ((Set.Finite.pi hS).preimage (f := fun (e : E) k => b.repr e k) ?_).subset ?_
    · intro x _ y _ hxy
      apply b.repr.injective
      ext k
      exact congrFun hxy k
    · intro e he k _
      refine ⟨inclR (AF F) e, he, ?_⟩
      exact repr_inclR (AF F) b e k
  · refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun y => φ y ⟨0, hd⟩ := by
      intro r
      obtain ⟨y, hy⟩ := hφ.surjective fun _ => r
      exact ⟨y, congrFun hy _⟩
    have := hK.image (hcont ⟨0, hd⟩)
    rwa [Set.image_univ, hsurj.range_eq] at this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n M`. Take `⟨⟨C, hCc, hCy⟩, hfin, hnc⟩` from `scalar F E σ h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C, isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hCc, ?_⟩` and prove the remaining obligations. Introduce `y`.

Use `choose X hX using fun a i => hCy (y a i)`. Conclude with `⟨X, fun a _ i _ => hX a i⟩`. Introduce `C hCc`. Establish `hcont : ∀ a i, Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i` using `fun a i => (continuous_apply i).comp (continuous_apply a)`. Establish `hS : ∀ a i, {e : E | inclR (AF F) e ∈ (fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i) '' C}.Finite` using `fun a i => hfin _ (hCc.image (hcont a i))`.

Use `(Set.Finite.pi fun a => Set.Finite.pi (hS a)).subset ?_` and prove the remaining obligations. Introduce `X hX a _ i _`. Conclude with `⟨ratTup (AF F) X, hX, rfl⟩`. Introduce `hn hM`. Use `⟨fun hK => hnc.noncompact_univ ?_⟩` and prove the remaining obligations.

Establish `hsurj : Function.Surjective fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩` using `fun r => ⟨fun _ _ => r, rfl⟩`. Establish `hc : Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩` using `(continuous_apply (⟨0, hM⟩ : Fin M)).comp (continuous_apply (⟨0, hn⟩ : Fin n))`. Use `hK.image hc` as an intermediate fact. Rewrite `this` using `[Set.image_univ, hsurj.range_eq]`. Then use the resulting hypothesis.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h n M
  obtain ⟨⟨C, hCc, hCy⟩, hfin, hnc⟩ := scalar F E σ h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hCc, ?_⟩
    intro y
    choose X hX using fun a i => hCy (y a i)
    exact ⟨X, fun a _ i _ => hX a i⟩
  · intro C hCc
    have hcont : ∀ a i, Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i :=
      fun a i => (continuous_apply i).comp (continuous_apply a)
    have hS : ∀ a i, {e : E | inclR (AF F) e ∈ (fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i) '' C}.Finite :=
      fun a i => hfin _ (hCc.image (hcont a i))
    refine (Set.Finite.pi fun a => Set.Finite.pi (hS a)).subset ?_
    intro X hX a _ i _
    exact ⟨ratTup (AF F) X, hX, rfl⟩
  · intro hn hM
    refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      fun r => ⟨fun _ _ => r, rfl⟩
    have hc : Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      (continuous_apply (⟨0, hM⟩ : Fin M)).comp (continuous_apply (⟨0, hn⟩ : Fin n))
    have := hK.image hc
    rwa [Set.image_univ, hsurj.range_eq] at this

end GlobalTheory.CompanionTheory.SW.CocW
