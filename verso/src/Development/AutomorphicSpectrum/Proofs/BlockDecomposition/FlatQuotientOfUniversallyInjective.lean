import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.FlatCoker

/- English proof (translation)
Establish `h1` using `LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor P i g) t`. Establish `h2` using `LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor P i g) t`. Conclude with `h1.trans h2.symm`.
-/
theorem lTensor_rTensor_comm {R P Q X Y : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (g : X →ₗ[R] Y) (t : P ⊗[R] X) :
    g.lTensor Q (i.rTensor X t) = i.rTensor Y (g.lTensor P t) := by
  have h1 := LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor P i g) t
  have h2 := LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor P i g) t
  exact h1.trans h2.symm

/- English proof (translation)
Rewrite using `[Module.Flat.iff_rTensor_injective']`. Introduce `I`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Establish `hRrow` using `lTensor_exact R (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective (LinearMap.range f))`.

Establish `hIrow` using `lTensor_exact (↥I) (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective (LinearMap.range f))`. Establish `hAcol` using `rTensor_exact A (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)`. Establish `hBcol` using `rTensor_exact B (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)`. Establish `hBinj : Function.Injective (LinearMap.rTensor B I.subtype)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)`. Take `⟨y, rfl⟩` from `LinearMap.lTensor_surjective (↥I) (Submodule.mkQ_surjective (LinearMap.range f)) z`.

Rewrite `hz` using `[← lTensor_rTensor_comm I.subtype (LinearMap.range f).mkQ y]`. Take `⟨x, hx⟩` from `(hRrow _).mp hz`. Establish `hq : LinearMap.lTensor (R ⧸ I) f (LinearMap.rTensor A I.mkQ x) = 0`. Rewrite using `[lTensor_rTensor_comm I.mkQ f x, hx]`. Conclude with `(hBcol _).mpr ⟨y, rfl⟩`.

Establish `hq0 : LinearMap.rTensor A I.mkQ x = 0` using `(injective_iff_map_eq_zero (LinearMap.lTensor (R ⧸ I) f)).mp (hf (R ⧸ I)) _ hq`. Take `⟨w, rfl⟩` from `(hAcol x).mp hq0`. Establish `hyw : LinearMap.lTensor (↥I) f w = y`. Apply `hBinj` to reduce the goal to its premises. Rewrite using `[← hx]`.

Conclude with `(lTensor_rTensor_comm I.subtype f w).symm`. Rewrite using `[← hyw]`. Conclude with `(hIrow _).mpr ⟨w, rfl⟩`.
-/
theorem flat_quotient_range_of_lTensor_injective
    (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) :
    Module.Flat R (B ⧸ LinearMap.range f) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hRrow := lTensor_exact R (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hIrow := lTensor_exact (↥I) (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hAcol := rTensor_exact A (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBcol := rTensor_exact B (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBinj : Function.Injective (LinearMap.rTensor B I.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (↥I)
    (Submodule.mkQ_surjective (LinearMap.range f)) z
  rw [← lTensor_rTensor_comm I.subtype (LinearMap.range f).mkQ y] at hz
  obtain ⟨x, hx⟩ := (hRrow _).mp hz
  have hq : LinearMap.lTensor (R ⧸ I) f (LinearMap.rTensor A I.mkQ x) = 0 := by
    rw [lTensor_rTensor_comm I.mkQ f x, hx]
    exact (hBcol _).mpr ⟨y, rfl⟩
  have hq0 : LinearMap.rTensor A I.mkQ x = 0 :=
    (injective_iff_map_eq_zero (LinearMap.lTensor (R ⧸ I) f)).mp (hf (R ⧸ I)) _ hq
  obtain ⟨w, rfl⟩ := (hAcol x).mp hq0
  have hyw : LinearMap.lTensor (↥I) f w = y := by
    apply hBinj
    rw [← hx]
    exact (lTensor_rTensor_comm I.subtype f w).symm
  rw [← hyw]
  exact (hIrow _).mpr ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.FlatCoker
