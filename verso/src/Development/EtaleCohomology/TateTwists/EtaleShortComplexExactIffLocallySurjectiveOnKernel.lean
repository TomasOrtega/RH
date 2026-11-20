import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKern

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

abbrev secF (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ Type 1 :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U) ⋙ forget _

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma etale_sheaf_sections_map_comp_hom {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma etale_sheaf_sections_map_zero_hom {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

/- English proof (translation)
Simplify `(NatTrans.naturality_apply φ.hom g.op x).symm` using `[Sec.map, Sec.res]`.
-/
lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  simpa [Sec.map, Sec.res] using (NatTrans.naturality_apply φ.hom g.op x).symm

/- English proof (translation)
Establish `w : (secF R U).map (kernel.ι g) ≫ (secF R U).map g = (secF R U).map (kernel.ι g) ≫ (secF R U).map 0`. Rewrite using `[← (secF R U).map_comp, ← (secF R U).map_comp, kernel.condition, comp_zero]`. Establish `hl : IsLimit (Fork.ofι _ w)` using `isLimitForkMapOfIsLimit (secF R U) _ (kernelIsKernel g)`. Establish `hu` using `Types.unique_of_type_equalizer _ _ hl`. Establish `hc : ∀ k : Sec (kernel g) U, Sec.map g (Sec.map (kernel.ι g) k) = 0`.

Introduce `k`. Rewrite using `[← etale_sheaf_sections_map_comp_hom, kernel.condition]`. Both sides reduce to the same expression. Use `⟨fun k₁ k₂ h => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨x, -, hx⟩` from `hu (Sec.map (kernel.ι g) k₁) ((hc k₁).trans (etale_sheaf_sections_map_zero_hom (G := G) _).symm)`.

Conclude with `(hx k₁ rfl).trans (hx k₂ h.symm).symm`. Take `⟨x, hx, -⟩` from `hu b (hb.trans (etale_sheaf_sections_map_zero_hom (G := G) b).symm)`. Conclude with `⟨x, hx⟩`.
-/
lemma kernel_sec {R : Type} [CommRing R] {F G : Shv R} (g : F ⟶ G) (U : Scheme.{0}) :
    Function.Injective (fun k : Sec (kernel g) U => Sec.map (kernel.ι g) k) ∧
    ∀ b : Sec F U, Sec.map g b = 0 → ∃ k, Sec.map (kernel.ι g) k = b := by
  have w : (secF R U).map (kernel.ι g) ≫ (secF R U).map g = (secF R U).map (kernel.ι g) ≫ (secF R U).map 0 := by
    rw [← (secF R U).map_comp, ← (secF R U).map_comp, kernel.condition, comp_zero]
  have hl : IsLimit (Fork.ofι _ w) := isLimitForkMapOfIsLimit (secF R U) _ (kernelIsKernel g)
  have hu := Types.unique_of_type_equalizer _ _ hl
  have hc : ∀ k : Sec (kernel g) U, Sec.map g (Sec.map (kernel.ι g) k) = 0 := by
    intro k; rw [← etale_sheaf_sections_map_comp_hom, kernel.condition]; rfl
  refine ⟨fun k₁ k₂ h => ?_, fun b hb => ?_⟩
  · obtain ⟨x, -, hx⟩ := hu (Sec.map (kernel.ι g) k₁) ((hc k₁).trans (etale_sheaf_sections_map_zero_hom (G := G) _).symm)
    exact (hx k₁ rfl).trans (hx k₂ h.symm).symm
  · obtain ⟨x, hx, -⟩ := hu b (hb.trans (etale_sheaf_sections_map_zero_hom (G := G) b).symm)
    exact ⟨x, hx⟩

/- English proof (translation)
Introduce `R _ S`. Rewrite using `[S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi']`. Establish `hl : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V), Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a`. Introduce `V a`. Rewrite using `[← etale_sheaf_sections_map_comp_hom, kernel.lift_ι]`.

Prove the components needed by the constructor for the conclusion. Introduce `h U b hb`. Take `⟨k, rfl⟩` from `(kernel_sec S.g U).2 b hb`. Use `⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (kernel.lift S.g S.f S.zero).hom (U := op U) k, ?_⟩` and prove the remaining obligations. Introduce and unpack `V g ⟨t, ht⟩`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← hl t, show Sec.map (kernel.lift S.g S.f S.zero) t = Sec.res g k from ht, sec_map_res]`. Introduce `h`. Prove the components needed by the constructor for the conclusion. Introduce `U k`.

Take `⟨T, hT, hTa⟩` from `h U (Sec.map (kernel.ι S.g) k) (by rw [← etale_sheaf_sections_map_comp_hom, kernel.condition]; rfl)`. Use `Scheme.etaleTopology.superset_covering ?_ hT` and prove the remaining obligations. Introduce `V g hg`. Take `⟨a, ha⟩` from `hTa V g hg`. Use `⟨a, (kernel_sec S.g V).1 ?_⟩` and prove the remaining obligations.

Conclude with `(hl a).trans (ha.trans (sec_map_res _ _ _).symm)`.
-/
theorem etale_short_complex_exact_iff_locally_surjective_on_kernel : EtaleShortComplexExactIffLocallySurjectiveOnKernel := by
  intro R _ S
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi']
  have hl : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := by
    intro V a; rw [← etale_sheaf_sections_map_comp_hom, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := (kernel_sec S.g U).2 b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (kernel.lift S.g S.f S.zero).hom (U := op U) k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hl t, show Sec.map (kernel.lift S.g S.f S.zero) t = Sec.res g k from ht, sec_map_res]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTa⟩ := h U (Sec.map (kernel.ι S.g) k)
      (by rw [← etale_sheaf_sections_map_comp_hom, kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTa V g hg
    refine ⟨a, (kernel_sec S.g V).1 ?_⟩
    exact (hl a).trans (ha.trans (sec_map_res _ _ _).symm)

end LateralTheory.EtaleFoundations
