import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataBis

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

/- English proof (translation)
Rewrite using `[gramO, Matrix.sub_apply, Matrix.mul_apply, diagonal_apply]`. Repeatedly rewrite using `[mul_diagonal, conjTranspose_apply]`. Apply the tactic sequence `split_ifs <;> simp [jK_star, map_sum]`.
-/
theorem gramO_apply {m : ℕ} (a : Fin m → 𝓞 F) (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (i j : Fin m) :
    jK (gramO a Y i j) = (∑ l, star (jK (Y l i)) * jK (ι (a l)) * jK (Y l j)) -
      if i = j then jK (ι (a i)) else 0 := by
  rw [gramO, Matrix.sub_apply, Matrix.mul_apply, diagonal_apply]
  simp_rw [mul_diagonal, conjTranspose_apply]
  split_ifs <;> simp [jK_star, map_sum]

def endoOf (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (g : V →ₗ[𝓞 K] V)
    (hA : ∀ x ∈ locF 𝔭 (dualIn h ⊤ L), g x ∈ locF 𝔭 (dualIn h ⊤ L))
    (hB : ∀ x ∈ locF 𝔭 L, g x ∈ locF 𝔭 L) : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  Submodule.mapQ _ _ (g.restrict hA) (fun _ hx => hB _ hx)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem endoOf_mk (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (g : V →ₗ[𝓞 K] V) (hA hB) (y : ↥(locF 𝔭 (dualIn h ⊤ L))) :
    endoOf h L 𝔭 g hA hB (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨g y, hA y y.2⟩ := rfl

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
  (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L)
include horth hdiag ha hbX hloc hF h𝔭 hL

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Rewrite `hx`, the goal using `[mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL]`. Introduce `k`. Rewrite using `[crd_gmap horth hdiag ha]`. Conclude with `sum_mem fun j _ => mul_mem (HU.jK_mem_SP _) (hx j)`.
-/
theorem gmap_B (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (hx : x ∈ locF 𝔭 L) :
    gmap h b a Y x ∈ locF 𝔭 L := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha]
  exact sum_mem fun j _ => mul_mem (HU.jK_mem_SP _) (hx j)

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Rewrite `hx`, the goal using `[mem_A horth hdiag ha hbX hloc hF h𝔭 hL]`. Introduce `k`. Rewrite using `[crd_gmap horth hdiag ha, Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Establish `e : jK (ι (a k) * Y k j) / jK (ι (a j)) * (jK (ι (a j)) * crd h b a x j) = jK (ι (a k)) * (jK (Y k j) * crd h b a x j)`. Rewrite using `[map_mul, div_mul_eq_mul_div, div_eq_iff (jK_ι_ne_zero (ha j))]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `mul_mem (hY k j) (hx j)`.
-/
theorem gmap_A (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := h𝔭.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭)
    (x : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) : gmap h b a Y x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  have e : jK (ι (a k) * Y k j) / jK (ι (a j)) * (jK (ι (a j)) * crd h b a x j) =
      jK (ι (a k)) * (jK (Y k j) * crd h b a x j) := by
    rw [map_mul, div_mul_eq_mul_div, div_eq_iff (jK_ι_ne_zero (ha j))]; ring
  rw [← e]
  exact mul_mem (hY k j) (hx j)

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Rewrite `hx` using `[mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL]`. Rewrite using `[mem_A horth hdiag ha hbX hloc hF h𝔭 hL]`. Conclude with `fun i => mul_mem (HU.jK_mem_SP _) (hx i)`.
-/
theorem B_le_A (x : V) (hx : x ∈ locF 𝔭 L) : x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL]
  exact fun i => mul_mem (HU.jK_mem_SP _) (hx i)

/- English proof (translation)
The claim follows from `h𝔭.isPrime; h x y ∈ HU.SP K 𝔭 ∧ h y x ∈ HU.SP K 𝔭 := by have := h𝔭.isPrime rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hy rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y, h_expand horth hdiag ha hbX hloc h𝔭.isPrime …`.
-/
theorem h_AB (x y : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 L) :
    haveI := h𝔭.isPrime; h x y ∈ HU.SP K 𝔭 ∧ h y x ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hy
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL y x]
  refine ⟨sum_mem fun i _ => ?_, sum_mem fun i _ => ?_⟩
  · have e : star (crd h b a x i) * jK (ι (a i)) * crd h b a y i =
        star (jK (ι (a i)) * crd h b a x i) * crd h b a y i := by
      rw [star_mul', star_jK_ι hF]; ring
    rw [e]
    exact mul_mem (star_mem_SP hF (hx i)) (hy i)
  · rw [mul_assoc]
    exact mul_mem (star_mem_SP hF (hy i)) (hx i)

/- English proof (translation)
Rewrite using `[h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y, h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL (gmap h b a Y x) (gmap h b a Y y)]`. Simplify using `only [crd_gmap horth hdiag ha, gramO_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]`. Use `congr 1`. Simplify using `only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_comm.trans ?_` and prove the remaining obligations.

Use `(Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_comm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem form_identity (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x y : V) :
    h (gmap h b a Y x) (gmap h b a Y y) - h x y =
      ∑ i, ∑ j, star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL (gmap h b a Y x) (gmap h b a Y y)]
  simp only [crd_gmap horth hdiag ha, gramO_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end Formalism.L2.SG.Pf.fibreCountingData
