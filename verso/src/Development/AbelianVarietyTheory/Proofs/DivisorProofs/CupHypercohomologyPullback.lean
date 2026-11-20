import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace CupPull

/- English proof (translation)
Use `ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x` as an intermediate fact. Simplify using `only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this
  exact this.symm

/- English proof (translation)
Introduce `N w hw U x`. Rewrite using `[CupSpec.ev_pull, h N w hw U (x.map f)]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]`.
-/
theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cochain ((chains R).obj E') I n} {β : Cochain ((chains R).obj E') J m}
    {γ : Cochain ((chains R).obj E') K k} (h : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w hw U x
  rw [CupSpec.ev_pull, h N w hw U (x.map f)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]

end CupPull

/- English proof (translation)
Introduce `R _ I J K μ E E' f n m k hk a b`. Take `⟨α, rfl⟩` from `a.mk_surjective`. Take `⟨β, rfl⟩` from `b.mk_surjective`. Take `⟨γ, hγ⟩` from `Pair.aw_exists μ E' hk α β`. Rewrite using `[Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]`.

Use `(Pair.cup_spec μ E hk _ _ _ ?_).symm` and prove the remaining obligations. Establish `e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f)` using `Cocycle.ofHom_coe _`. Simplify using `only [zcomp, Cocycle.mk_coe, e]`. Conclude with `CupPull.isAW_pull μ f hk hγ`.
-/
theorem Pair.cup_pull : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  intro R _ I J K μ E E' f n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := Pair.aw_exists μ E' hk α β
  rw [Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]
  refine (Pair.cup_spec μ E hk _ _ _ ?_).symm
  have e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f) :=
    Cocycle.ofHom_coe _
  simp only [zcomp, Cocycle.mk_coe, e]
  exact CupPull.isAW_pull μ f hk hγ

end GlobalTheory.EtC
