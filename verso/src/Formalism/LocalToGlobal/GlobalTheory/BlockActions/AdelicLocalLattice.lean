import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InclEMemTensInt

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Lat

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

/- English proof (translation)
Use `set S := tensInt (F := F) R (intOE E) S₂`. Use `set G : Fin k → (Fin n → E ⊗[F] R) := fun i l => inclE (F := F) R (g i l)`. Establish `hle : latS (F` using `F) R S Λ ≤ Submodule.span S (Set.range G) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Rewrite `hx` using `[← hg]`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx`. Establish `: (fun l => inclE (F` using `F) R ((∑ i, a i • g i) l)) = ∑ i, (⟨inclE (F := F) R (algebraMap (𝓞 E) E (a i)), inclE_mem_tensInt (F := F) (R := R) (S₂ := S₂) (a i)⟩ : S) • G i := by`. Use function extensionality and compare the values at `l`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]`. Use `show (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) ∈ Submodule.span S (Set.range G)`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Take `⟨s, hs⟩` from `(Submodule.mem_span_range_iff_exists_fun S).1 (hle hy)`. Use `choose r hr hsr using fun i => tq_decomp (F := F) (R := R) (S₂ := S₂) b hb (s i).2`. Use `⟨r, hr, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[← hs, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul, hsr i, Finset.sum_mul]`.
-/
theorem latS_decomp {m k : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (g : Fin k → (Fin n → E))
    (hg : Submodule.span (𝓞 E) (Set.range g) = Λ) (y : Fin n → E ⊗[F] R)
    (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ) :
    ∃ r : Fin k → Fin m → R, (∀ i j, r i j ∈ S₂) ∧ ∀ l, y l =
      ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r i j) * inclE (F := F) R (g i l) := by
  set S := tensInt (F := F) R (intOE E) S₂
  set G : Fin k → (Fin n → E ⊗[F] R) := fun i l => inclE (F := F) R (g i l)
  have hle : latS (F := F) R S Λ ≤ Submodule.span S (Set.range G) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
    have : (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) =
        ∑ i, (⟨inclE (F := F) R (algebraMap (𝓞 E) E (a i)), inclE_mem_tensInt (F := F) (R := R) (S₂ := S₂) (a i)⟩ : S) • G i := by
      funext l
      rw [Finset.sum_apply, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) ∈ Submodule.span S (Set.range G)
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (hle hy)
  choose r hr hsr using fun i => tq_decomp (F := F) (R := R) (S₂ := S₂) b hb (s i).2
  refine ⟨r, hr, fun l => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, hsr i, Finset.sum_mul]

end Lat

section Glue

variable {F : Type} [Field F] [NumberField F]

def glueInt (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨r, Filter.Eventually.of_forall hr⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glueInt_apply (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    glueInt r hr v = r v := rfl

/- English proof (translation)
Use `first`. Consider the case `exact fun v => hr v`. Consider the case `(intro v; simpa [glueInt_apply] using hr v)`. Consider the case `(simp only [intAd]; intro v; exact hr v)`. Consider the case `simp [intAd, glueInt_apply, hr]`.

Consider the case `(unfold intAd; guard_target =ₛ True)`.
-/
theorem glueInt_mem (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : glueInt r hr ∈ intAd F := by
  first
  | exact fun v => hr v
  | (intro v; simpa [glueInt_apply] using hr v)
  | (simp only [intAd]; intro v; exact hr v)
  | simp [intAd, glueInt_apply, hr]
  | (unfold intAd; guard_target =ₛ True)

end Glue

/- English proof (translation)
Introduce `F E _ _ _ _ _ n Λ hΛ x hx`. Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Take `⟨k, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (Module.Finite.iff_fg.1 hΛ)`. Use `choose r hr hxr using fun v : HeightOneSpectrum (𝓞 F) => latS_decomp (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring b hb Λ g hg _ (hx v)`. Use `set Rg : Fin k → Fin m → FiniteAdeleRing (𝓞 F) F := fun i j => glueInt (fun v => r v i j) (fun v => hr v i j) with hRg`.

Establish `hx' : x = fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) * inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (g i l) := by`. Use function extensionality and compare the values at `l`. Rewrite using `[← sub_eq_zero]`. Use `Formalism.UG.P.afsplit_inj _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`.

Use `(hxr v l).trans ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hgΛ : ∀ i, g i ∈ Λ` using `fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hmem : ∀ i j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j ∈ tensInt (F` using `F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := fun i j => tensInt_tmul_mem (b j) (glueInt_mem _ _)`. Establish `hsum : (fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) * inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (g i l)) = ∑ i, ∑ j, (⟨_, hmem i j⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) • (fun l => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) := by`.

Use function extensionality and compare the values at `l`. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Rewrite using `[hx', hsum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hgΛ i, rfl⟩)`.
-/
theorem adelic_local_lattice : AdLocLat := by
  intro F E _ _ _ _ _ n Λ hΛ x hx
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (Module.Finite.iff_fg.1 hΛ)
  choose r hr hxr using fun v : HeightOneSpectrum (𝓞 F) =>
    latS_decomp (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring b hb Λ g hg _ (hx v)
  set Rg : Fin k → Fin m → FiniteAdeleRing (𝓞 F) F :=
    fun i j => glueInt (fun v => r v i j) (fun v => hr v i j) with hRg
  have hx' : x = fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l) := by
    funext l
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    rw [map_sub, sub_eq_zero]
    refine (hxr v l).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl
  have hgΛ : ∀ i, g i ∈ Λ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := fun i j =>
    tensInt_tmul_mem (b j) (glueInt_mem _ _)
  have hsum : (fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) =
      ∑ i, ∑ j, (⟨_, hmem i j⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun l => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) := by
    funext l
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  rw [hx', hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hgΛ i, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.Br
