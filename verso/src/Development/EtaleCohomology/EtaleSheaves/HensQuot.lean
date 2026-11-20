import Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6

noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfQuot
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

/- English proof (translation)
Establish `hloc : IsLocalHom g` using `IsLocalHom.of_surjective g hg`. Use `{ is_henselian := ?_ }` and prove the remaining obligations. Introduce `p hp a0 h0 h1`. Take `⟨P, hPmap, -, hPm⟩` from `Polynomial.lifts_and_degree_eq_and_monic (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp`. Take `⟨b0, rfl⟩` from `hg a0`.

Establish `e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x)` using `fun Q x => by`. Rewrite using `[Polynomial.eval_map, eval₂_at_apply]`. Establish `hb0 : P.eval b0 ∈ maximalIdeal A`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Use `hu.map g` as an intermediate fact. Rewrite `this` using `[e, hPmap]`. Conclude with `(mem_maximalIdeal _).mp h0 this`. Establish `hb1 : IsUnit ((derivative P).eval b0)`. Apply `(isUnit_map_iff g _).mp` to reduce the goal to its premises.

Rewrite using `[e, ← derivative_map, hPmap]`. Conclude with `h1`. Take `⟨b, hb, hbm⟩` from `HenselianLocalRing.is_henselian P hPm b0 hb0 hb1`. Use `⟨g b, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p.eval (g b) = 0`.

Rewrite using `[← hPmap, ← e, hb.eq_zero, map_zero]`. Rewrite using `[← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Conclude with `(mem_maximalIdeal _).mp hbm`.
-/
theorem hensQuot {A C : Type} [CommRing A] [HenselianLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) : HenselianLocalRing C := by
  have hloc : IsLocalHom g := IsLocalHom.of_surjective g hg
  refine { is_henselian := ?_ }
  intro p hp a0 h0 h1
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp
  obtain ⟨b0, rfl⟩ := hg a0
  have e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x) := fun Q x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  have hb0 : P.eval b0 ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map g
    rw [e, hPmap] at this
    exact (mem_maximalIdeal _).mp h0 this
  have hb1 : IsUnit ((derivative P).eval b0) := by
    apply (isUnit_map_iff g _).mp
    rw [e, ← derivative_map, hPmap]; exact h1
  obtain ⟨b, hb, hbm⟩ := HenselianLocalRing.is_henselian P hPm b0 hb0 hb1
  refine ⟨g b, ?_, ?_⟩
  · change p.eval (g b) = 0
    rw [← hPmap, ← e, hb.eq_zero, map_zero]
  · rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp hbm

/- English proof (translation)
Establish `hbij : Function.Bijective (ResidueField.map g)`. Use `⟨(ResidueField.map g).injective, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨c, rfl⟩` from `residue_surjective y`. Take `⟨a, rfl⟩` from `hg c`.

Conclude with `⟨residue A a, by simp⟩`. Set `e` to `RingEquiv.ofBijective _ hbij`. Use `IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)` and prove the remaining obligations. Take `⟨x, hx⟩` from `IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A) e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep`. Use `⟨e x, ?_⟩` and prove the remaining obligations.

Establish `h2` using `congrArg e hx`. Rewrite `h2` using `[map_zero]`. Rewrite `h2` using `[show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl, Polynomial.hom_eval₂, RingEquiv.comp_symm]`. Conclude with `h2`.
-/
theorem sepQuot {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) [IsLocalHom g] [IsSepClosed (ResidueField A)] : IsSepClosed (ResidueField C) := by
  have hbij : Function.Bijective (ResidueField.map g) := by
    refine ⟨(ResidueField.map g).injective, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨residue A a, by simp⟩
  let e := RingEquiv.ofBijective _ hbij
  refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A)
    e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep
  refine ⟨e x, ?_⟩
  have h2 := congrArg e hx
  rw [map_zero] at h2
  rw [show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl,
    Polynomial.hom_eval₂, RingEquiv.comp_symm] at h2
  exact h2

/- English proof (translation)
Introduce `A _ hA W' ι' _`. Take `⟨hH, hS⟩` from `hA`. Take `⟨hAff, hsurj⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine ι'`. Set `g : CommRingCat.of A ⟶ Γ(W', ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop`. Establish `hg : Function.Surjective g` using `hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective`.

Distinguish the cases in `hC : Nontrivial Γ(W', ⊤)`. Use `right`. Establish `hLC : IsLocalRing Γ(W', ⊤)` using `IsLocalRing.of_surjective' g.hom hg`. Establish `hHC` using `hensQuot g.hom hg`. Establish `: IsLocalHom g.hom` using `IsLocalHom.of_surjective g.hom hg`.

Conclude with `⟨hHC, sepQuot g.hom hg⟩`. Use `left`. Rewrite `hC` using `[not_nontrivial_iff_subsingleton]`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h10 : (1 : Γ(W', ⊤)) = 0` using `Subsingleton.elim _ _`.

Use `congrArg (W'.presheaf.germ ⊤ x trivial).hom h10` as an intermediate fact. Rewrite `this` using `[map_one, map_zero]`. Conclude with `one_ne_zero this`.
-/
theorem shQuot : LeafSHQuot := by
  intro A _ hA W' ι' _
  obtain ⟨hH, hS⟩ := hA
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g :=
    hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  by_cases hC : Nontrivial Γ(W', ⊤)
  · right
    have hLC : IsLocalRing Γ(W', ⊤) := IsLocalRing.of_surjective' g.hom hg
    have hHC := hensQuot g.hom hg
    have : IsLocalHom g.hom := IsLocalHom.of_surjective g.hom hg
    exact ⟨hHC, sepQuot g.hom hg⟩
  · left
    rw [not_nontrivial_iff_subsingleton] at hC
    refine ⟨fun x => ?_⟩
    have h10 : (1 : Γ(W', ⊤)) = 0 := Subsingleton.elim _ _
    have := congrArg (W'.presheaf.germ ⊤ x trivial).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this

end LateralTheory.E.LeafClosedSH0PfQuot
