import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I`. Use `letI := o.grp`. Use `letI := o₁.grp`. Use `letI := o.comm`. Establish `hl : ∀ x : Over.mk t ⟶ o₁.A, Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ` using `fun _ => rfl`.

Set `E` to `MulEquiv.ofBijective (pushHom m.cart (Over.mk t)) ⟨push_injective m.cart _, push_surjective m.cart _⟩`. Establish `key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q` using `fun q => by`. Rewrite using `[← hl]`. Conclude with `congrArg Over.Hom.left (E.apply_symm_apply q)`. Use `⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => E.symm (I.ev n y), add := fun n x y => by simp only [I.add, map_mul], lin := fun n c x => ?_, ker := fun n hn x => by` and prove the remaining obligations.

Rewrite using `[← I.ker n hn x]`. Conclude with `E.symm.map_eq_one_iff,`. Use `onto := fun n hn q => ?_,`. Use `tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],`. Use `isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩`.

Establish `h1` using `push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))`. Establish `h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x` using `E.apply_symm_apply _`. Rewrite `h1` using `[h2]`. Apply `E.injective` to reduce the goal to its premises. Rewrite using `[E.apply_symm_apply, I.lin]`.

Conclude with `h1.symm`. Prove the components needed by the constructor for the conclusion. Introduce `hq`. Take `⟨x, hx⟩` from `(I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])`. Conclude with `⟨x, by rw [hx, E.symm_apply_apply]⟩`.

Introduce and unpack `⟨x, rfl⟩`. Rewrite using `[← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]`. Conclude with `(weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _) m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2 (I.isom n hn x y)`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.tatePull_of :
    TatePull := by
  intro p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I
  letI := o.grp
  letI := o₁.grp
  letI := o.comm
  have hl : ∀ x : Over.mk t ⟶ o₁.A,
      Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ := fun _ => rfl
  let E := MulEquiv.ofBijective (pushHom m.cart (Over.mk t))
    ⟨push_injective m.cart _, push_surjective m.cart _⟩
  have key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q := fun q => by
    rw [← hl]
    exact congrArg Over.Hom.left (E.apply_symm_apply q)
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n y => E.symm (I.ev n y),
            add := fun n x y => by simp only [I.add, map_mul],
            lin := fun n c x => ?_,
            ker := fun n hn x => by
              rw [← I.ker n hn x]
              exact E.symm.map_eq_one_iff,
            onto := fun n hn q => ?_,
            tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],
            isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩
  · have h1 := push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))
    have h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x := E.apply_symm_apply _
    rw [h2] at h1
    apply E.injective
    rw [E.apply_symm_apply, I.lin]
    exact h1.symm
  · constructor
    · intro hq
      obtain ⟨x, hx⟩ := (I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])
      exact ⟨x, by rw [hx, E.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]
  · exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _)
      m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2
      (I.isom n hn x y)
