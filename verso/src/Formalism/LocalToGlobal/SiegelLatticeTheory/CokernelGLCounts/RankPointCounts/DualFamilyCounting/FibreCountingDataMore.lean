import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataTer

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
Rewrite using `[div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hz]`.
-/
theorem div_mul_mul' {x y z : K} (hz : z ≠ 0) : x / z * (z * y) = x * y := by
  rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hz]

structure JD (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {m : ℕ}
    (b : Fin m → V) (a : Fin m → 𝓞 F) : Prop where
  orth : ∀ i j, i ≠ j → h (b i) (b j) = 0
  diag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)
  ne : ∀ i, a i ≠ 0
  loc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L
  fix : IsFixF K F
  max : 𝔭.IsMaximal
  lat : IsLatIn ⊤ L

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

/- English proof (translation)
Introduce `_` and use `Submodule.mem_top`.
-/
theorem bX : ∀ i, b i ∈ (⊤ : Submodule K V) := fun _ => Submodule.mem_top

/- English proof (translation)
The claim follows from `J.max.isPrime; crd h b a x i ∈ HU.SP K 𝔭 := mem_B J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat x`.
-/
theorem memB (x : V) : x ∈ locF 𝔭 L ↔ ∀ i, haveI := J.max.isPrime; crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_B J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat x

/- English proof (translation)
The claim follows from `J.max.isPrime; jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 := mem_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat x`.
-/
theorem memA (x : V) : x ∈ locF 𝔭 (dualIn h ⊤ L) ↔
    ∀ i, haveI := J.max.isPrime; jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 :=
  mem_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat x

/- English proof (translation)
The claim follows from `crd_gmap J.orth J.diag J.ne Y x k`.
-/
theorem crdG (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j :=
  crd_gmap J.orth J.diag J.ne Y x k

/- English proof (translation)
The claim follows from `J.max.isPrime; h x' y' - h x y ∈ HU.SP K 𝔭 := by have := J.max.isPrime have hAB := h_AB J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat have e : h x' y' - h x y = h x (y' - y) + h (x' - x) y + h (x' - x) (y' - y) := by simp only [map_sub, LinearMap.sub_apply]; ring rw [e] refine …`.
-/
theorem h_sub_mem (x y x' y' : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 (dualIn h ⊤ L))
    (hx' : x' - x ∈ locF 𝔭 L) (hy' : y' - y ∈ locF 𝔭 L) :
    haveI := J.max.isPrime; h x' y' - h x y ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have hAB := h_AB J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat
  have e : h x' y' - h x y = h x (y' - y) + h (x' - x) y + h (x' - x) (y' - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem (hAB x _ hx hy').1 (hAB y _ hy hx').2) (hAB _ _ ?_ hy').1
  exact B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ hx'

def E (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  endoOf h L 𝔭 (gmap h b a Y) (gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY)
    (gmap_B J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem E_mk (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY) (x : ↥(locF 𝔭 (dualIn h ⊤ L))) :
    J.E Y hY (Submodule.Quotient.mk x) = Submodule.Quotient.mk
      ⟨gmap h b a Y x, gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY x x.2⟩ := rfl

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Introduce `x y x' y' hx hy`. Rewrite `hx`, `hy` using `[E_mk, Submodule.Quotient.eq, Submodule.mem_comap]`. Simplify using `only [Submodule.subtype_apply, Submodule.coe_sub] at hx hy`. Establish `gA` using `gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY`.

Rewrite using `[← HU.mem_SP_iff_locF]`. Establish `e : h (x' : V) (y' : V) - h (x : V) (y : V) = (h (x' : V) (y' : V) - h (gmap h b a Y x) (gmap h b a Y y)) + (h (gmap h b a Y x) (gmap h b a Y y) - h (x : V) (y : V))` using `by ring`. Rewrite using `[e]`. Use `add_mem (J.h_sub_mem _ _ _ _ (gA _ x.2) (gA _ y.2) hx hy) ?_` and prove the remaining obligations. Rewrite using `[form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]`.

Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `hxA` using `(J.memA x).1 x.2 i`. Establish `hyA` using `(J.memA y).1 y.2 j`. Establish `hne : jK (ι (a i)) * jK (ι (a j)) ≠ 0` using `mul_ne_zero (jK_ι_ne_zero (J.ne i)) (jK_ι_ne_zero (J.ne j))`. Establish `e2 : star (jK (ι (a i)) * crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) * (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j`.

Rewrite using `[star_mul', star_jK_ι J.fix, show jK (ι (a i)) * star (crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) * (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j * ((jK (ι (a i)) * jK (ι (a j))) / (jK (ι (a i)) * jK (ι (a j) …`. Rewrite using `[← e2]`. Conclude with `mul_mem (mul_mem (star_mem_SP J.fix hxA) (hW i j)) hyA`.
-/
theorem E_isom (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (hY)
    (hW : ∀ i j, haveI := J.max.isPrime;
      jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) :
    ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = J.E Y hY (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = J.E Y hY (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := J.max.isPrime
  intro x y x' y' hx hy
  rw [E_mk, Submodule.Quotient.eq, Submodule.mem_comap] at hx hy
  simp only [Submodule.subtype_apply, Submodule.coe_sub] at hx hy
  have gA := gmap_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat Y hY
  rw [← HU.mem_SP_iff_locF]
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      (h (x' : V) (y' : V) - h (gmap h b a Y x) (gmap h b a Y y)) +
        (h (gmap h b a Y x) (gmap h b a Y y) - h (x : V) (y : V)) := by ring
  rw [e]
  refine add_mem (J.h_sub_mem _ _ _ _ (gA _ x.2) (gA _ y.2) hx hy) ?_
  rw [form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have hxA := (J.memA x).1 x.2 i
  have hyA := (J.memA y).1 y.2 j
  have hne : jK (ι (a i)) * jK (ι (a j)) ≠ 0 := mul_ne_zero (jK_ι_ne_zero (J.ne i)) (jK_ι_ne_zero (J.ne j))
  have e2 : star (jK (ι (a i)) * crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
      (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
    rw [star_mul', star_jK_ι J.fix,
      show jK (ι (a i)) * star (crd h b a x i) * (jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j)))) *
        (jK (ι (a j)) * crd h b a y j) = star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j *
          ((jK (ι (a i)) * jK (ι (a j))) / (jK (ι (a i)) * jK (ι (a j)))) by ring,
      div_self hne, mul_one]
  rw [← e2]
  exact mul_mem (mul_mem (star_mem_SP J.fix hxA) (hW i j)) hyA

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, E_mk]`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]`.

Rewrite using `[J.memB]`. Introduce `k`. Rewrite using `[crd_sub, J.crdG, J.crdG, ← Finset.sum_sub_distrib]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul, ← map_sub, ← div_mul_mul' (jK_ι_ne_zero (J.ne j))]`.

Conclude with `mul_mem (hd k j) ((J.memA x).1 x.2 j)`.
-/
theorem E_eq_of (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY')
    (hd : ∀ i j, haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭) :
    J.E Y hY = J.E Y' hY' := by
  have := J.max.isPrime
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, E_mk]
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
  rw [J.memB]
  intro k
  rw [crd_sub, J.crdG, J.crdG, ← Finset.sum_sub_distrib]
  refine sum_mem fun j _ => ?_
  rw [← sub_mul, ← map_sub, ← div_mul_mul' (jK_ι_ne_zero (J.ne j))]
  exact mul_mem (hd k j) ((J.memA x).1 x.2 j)

/- English proof (translation)
Rewrite using `[crd, h_phi J.orth J.diag J.ne]`. Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`.
-/
theorem crd_u (j l : Fin m) :
    crd h b a (phi (K := K) b a (Pi.single j 1)) l = if l = j then 1 / jK (ι (a j)) else 0 := by
  rw [crd, h_phi J.orth J.diag J.ne]
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_apply, hl]

/- English proof (translation)
Use `J.max.isPrime` as an intermediate fact. Rewrite using `[J.memA]`. Introduce `i`. Rewrite using `[← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]`. Conclude with `HU.jK_mem_SP _`.
-/
theorem u_mem (j : Fin m) : phi (K := K) b a (Pi.single j 1) ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[J.crd_u, if_pos rfl, mul_one_div]`. Introduce `l _ hl`. Rewrite using `[J.crd_u, if_neg hl, mul_zero]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ j) hj`.
-/
theorem sum_crd_u (f : Fin m → K) (j : Fin m) :
    ∑ l, f l * crd h b a (phi (K := K) b a (Pi.single j 1)) l = f j / jK (ι (a j)) := by
  rw [Finset.sum_eq_single j]
  · rw [J.crd_u, if_pos rfl, mul_one_div]
  · intro l _ hl; rw [J.crd_u, if_neg hl, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/- English proof (translation)
The claim follows from `J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by have := J.max.isPrime have h1 := congrArg (fun f => f (Submodule.Quotient.mk ⟨_, J.u_mem j⟩)) he simp only [E_mk] at h1 rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, …`.
-/
theorem entry_of_E_eq (Y Y' : Matrix (Fin m) (Fin m) (𝓞 K)) (hY hY') (he : J.E Y hY = J.E Y' hY')
    (i j : Fin m) : haveI := J.max.isPrime; jK (Y i j - Y' i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  have h1 := congrArg (fun f => f (Submodule.Quotient.mk ⟨_, J.u_mem j⟩)) he
  simp only [E_mk] at h1
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    J.memB] at h1
  have h2 := h1 i
  rw [crd_sub, J.crdG, J.crdG, J.sum_crd_u, J.sum_crd_u, ← sub_div, ← map_sub] at h2
  exact h2

end JD

end Formalism.L2.SG.Pf.fibreCountingData
