import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.LocalToGlobal.Columns.Inputs

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn princAt resS intGL frGL)

section RedALemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable instance kPField (P : Pl E) : Field (kP P) :=
  @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iA_coe (s : 𝓞 E) :
    iA F E (algebraMap (𝓞 E) E s) = ((Formalism.L2.DIV.oToS F E s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := rfl

/- English proof (translation)
Rewrite using `[iA_coe]`. Conclude with `SetLike.coe_mem _`.
-/
theorem iA_mem (s : 𝓞 E) : iA F E (algebraMap (𝓞 E) E s) ∈ Formalism.L2.Herm.intAf F E := by
  rw [iA_coe]
  exact SetLike.coe_mem _

/- English proof (translation)
Establish `h1 : Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * c) = Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * c')`. Rewrite using `[hc, hc', ← Formalism.L2.DIV.resS_oToS (F := F) P s', ← Formalism.L2.DIV.resS_oToS (F := F) P s, ← map_mul, ← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, Subtype.coe_mk, ← iA_coe]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Establish `hs0' : (Ideal.Quotient.mk P.asIdeal s' : kP P) ≠ 0` using `fun h => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Establish `h2 : (Ideal.Quotient.mk P.asIdeal s : kP P) * Ideal.Quotient.mk P.asIdeal s' * c = (Ideal.Quotient.mk P.asIdeal s : kP P) * Ideal.Quotient.mk P.asIdeal s' * c'`. Rewrite using `[mul_assoc, mul_assoc, ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ (mul_ne_zero hs0 hs0') h2`.
-/
private theorem redA_uniq_lemma (P : Pl E) {a : E ⊗[F] Formalism.L2.Herm.Af F} {s s' : 𝓞 E} (hs : s ∉ P.asIdeal)
    (hs' : s' ∉ P.asIdeal) (hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E)
    (hm' : iA F E (algebraMap (𝓞 E) E s') * a ∈ Formalism.L2.Herm.intAf F E) {c c' : kP P}
    (hc : Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩)
    (hc' : Ideal.Quotient.mk P.asIdeal s' * c' = resS F P ⟨_, hm'⟩) : c = c' := by
  have h1 : Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * c) =
      Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * c') := by
    rw [hc, hc', ← Formalism.L2.DIV.resS_oToS (F := F) P s', ← Formalism.L2.DIV.resS_oToS (F := F) P s, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, Subtype.coe_mk, ← iA_coe]
    ring
  have hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hs0' : (Ideal.Quotient.mk P.asIdeal s' : kP P) ≠ 0 := fun h => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h2 : (Ideal.Quotient.mk P.asIdeal s : kP P) * Ideal.Quotient.mk P.asIdeal s' * c =
      (Ideal.Quotient.mk P.asIdeal s : kP P) * Ideal.Quotient.mk P.asIdeal s' * c' := by
    rw [mul_assoc, mul_assoc, ← h1]
    ring
  exact mul_left_cancel₀ (mul_ne_zero hs0 hs0') h2

/- English proof (translation)
Establish `hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Establish `hc : Ideal.Quotient.mk P.asIdeal s * ((Ideal.Quotient.mk P.asIdeal s : kP P)⁻¹ * resS F P ⟨_, hm⟩) = resS F P ⟨_, hm⟩`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hs0, one_mul]`. Establish `hex : ∃ c : kP P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩` using `⟨_, s, hs, hm, hc⟩`. Establish `hr : redA P a = hex.choose`.

Unfold `redA`. Rewrite using `[dif_pos hex]`. Take `⟨s₀, hs₀, hm₀, h₀⟩` from `hex.choose_spec`. Rewrite using `[hr, redA_uniq_lemma P hs₀ hs hm₀ hm h₀ hc, hc]`.
-/
theorem redA_spec (P : Pl E) {a : E ⊗[F] Formalism.L2.Herm.Af F} {s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E) :
    Ideal.Quotient.mk P.asIdeal s * redA P a = resS F P ⟨_, hm⟩ := by
  have hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hc : Ideal.Quotient.mk P.asIdeal s * ((Ideal.Quotient.mk P.asIdeal s : kP P)⁻¹ * resS F P ⟨_, hm⟩) =
      resS F P ⟨_, hm⟩ := by
    rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  have hex : ∃ c : kP P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E,
      Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩ := ⟨_, s, hs, hm, hc⟩
  have hr : redA P a = hex.choose := by
    unfold redA
    rw [dif_pos hex]
  obtain ⟨s₀, hs₀, hm₀, h₀⟩ := hex.choose_spec
  rw [hr, redA_uniq_lemma P hs₀ hs hm₀ hm h₀ hc, hc]

/- English proof (translation)
Conclude with `redA_uniq_lemma P hs hs hm hm (redA_spec P hs hm) hc`.
-/
theorem redA_eq (P : Pl E) {a : E ⊗[F] Formalism.L2.Herm.Af F} {s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (hm : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E) {c : kP P}
    (hc : Ideal.Quotient.mk P.asIdeal s * c = resS F P ⟨_, hm⟩) : redA P a = c := by
  exact redA_uniq_lemma P hs hs hm hm (redA_spec P hs hm) hc

/- English proof (translation)
Establish `hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0` using `fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * e = algebraMap (𝓞 E) E r ∧ Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r` using `⟨(Ideal.Quotient.mk P.asIdeal s : kP P)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, h, by`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hs0, one_mul]⟩`. Establish `hr : redP P e = hex.choose`. Unfold `redP`.

Rewrite using `[dif_pos hex]`. Take `⟨r₀, s₀, hs₀, he₀, h₀⟩` from `hex.choose_spec`. Establish `hm : iA F E (algebraMap (𝓞 E) E s₀) * iA F E e ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[← map_mul, he₀]`. Conclude with `iA_mem r₀`.

Rewrite using `[hr]`. Apply `redA_eq P hs₀ hm` to reduce the goal to its premises. Rewrite using `[h₀, ← Formalism.L2.DIV.resS_oToS (F := F) P r₀]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← iA_coe, ← he₀, map_mul]`.
-/
theorem redA_iA (P : Pl E) {e : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : algebraMap (𝓞 E) E s * e = algebraMap (𝓞 E) E r) :
    redA P (iA F E e) = redP P e := by
  have hs0 : (Ideal.Quotient.mk P.asIdeal s : kP P) ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * e = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨(Ideal.Quotient.mk P.asIdeal s : kP P)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, h, by
      rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul]⟩
  have hr : redP P e = hex.choose := by
    unfold redP
    rw [dif_pos hex]
  obtain ⟨r₀, s₀, hs₀, he₀, h₀⟩ := hex.choose_spec
  have hm : iA F E (algebraMap (𝓞 E) E s₀) * iA F E e ∈ Formalism.L2.Herm.intAf F E := by
    rw [← map_mul, he₀]
    exact iA_mem r₀
  rw [hr]
  apply redA_eq P hs₀ hm
  rw [h₀, ← Formalism.L2.DIV.resS_oToS (F := F) P r₀]
  congr 1
  apply Subtype.ext
  rw [← iA_coe, ← he₀, map_mul]

/- English proof (translation)
Establish `hm : iA F E (algebraMap (𝓞 E) E s) * (∑ j, (y j : E ⊗[F] Formalism.L2.Herm.Af F) * u j) ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (y j).2 (hu j)`.

Apply `redA_eq P hs hm` to reduce the goal to its premises. Establish `e1 : ∀ j, Ideal.Quotient.mk P.asIdeal s * (resS F P (y j) * redA P (u j)) = resS F P (y j * ⟨_, hu j⟩)`. Introduce `j`. Rewrite using `[mul_left_comm (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs (hu j), map_mul]`. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun j _ => e1 j, ← map_sum]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Subtype.coe_mk]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem redA_sum {ι : Type} [Fintype ι] (P : Pl E) {s : 𝓞 E} (hs : s ∉ P.asIdeal) (u : ι → E ⊗[F] Formalism.L2.Herm.Af F)
    (hu : ∀ j, iA F E (algebraMap (𝓞 E) E s) * u j ∈ Formalism.L2.Herm.intAf F E) (y : ι → Formalism.L2.Herm.intAf F E) :
    redA P (∑ j, (y j : E ⊗[F] Formalism.L2.Herm.Af F) * u j) = ∑ j, resS F P (y j) * redA P (u j) := by
  have hm : iA F E (algebraMap (𝓞 E) E s) * (∑ j, (y j : E ⊗[F] Formalism.L2.Herm.Af F) * u j) ∈ Formalism.L2.Herm.intAf F E := by
    rw [Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact mul_mem (y j).2 (hu j)
  apply redA_eq P hs hm
  have e1 : ∀ j, Ideal.Quotient.mk P.asIdeal s * (resS F P (y j) * redA P (u j)) =
      resS F P (y j * ⟨_, hu j⟩) := by
    intro j
    rw [mul_left_comm (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs (hu j), map_mul]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => e1 j, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Subtype.coe_mk]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end RedALemmas

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Unfold `stdLat Formalism.UG.stdLat`. Rewrite using `[Submodule.one_eq_range]`.
-/
theorem stdLat_eq_ug : stdLat E n = Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E) := by
  unfold stdLat Formalism.UG.stdLat
  rw [Submodule.one_eq_range]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Formalism.UG.latS, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)` using `hx`. Use `show _ ∈ Submodule.pi Set.univ fun _ : Fin n => LinearMap.range (Algebra.linearMap (Formalism.L2.Herm.intAf F E) (E ⊗[F] Formalism.L2.Herm.Af F))`.

Use `Submodule.mem_pi.2 fun i _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.1 (Submodule.mem_pi.1 hx' i (Set.mem_univ i))`. Conclude with `LinearMap.mem_range.2 ⟨Formalism.L2.DIV.oToS F E r, congrArg (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) hr⟩`. Introduce `z hz`. Establish `hz' : z ∈ Submodule.pi Set.univ fun _ : Fin n => LinearMap.range (Algebra.linearMap (Formalism.L2.Herm.intAf F E) (E ⊗[F] Formalism.L2.Herm.Af F))` using `hz`.

Use `choose y hy using fun i => LinearMap.mem_range.1 (Submodule.mem_pi.1 hz' i (Set.mem_univ i))`. Establish `e : z = ∑ i, y i • (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j))`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (fun h => absurd (Finset.mem_univ j) h)]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, map_one]`.

Rewrite using `[← hy j, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (y i) (Submodule.subset_span ⟨Pi.single i 1, ?_, rfl⟩)` and prove the remaining obligations. Use `show Pi.single i (1 : E) ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)`. Use `Submodule.mem_pi.2 fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Conclude with `Submodule.zero_mem _`.
-/
theorem latS_std : Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) =
    Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) := by
  apply le_antisymm
  · rw [Formalism.UG.latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) := hx
    show _ ∈ Submodule.pi Set.univ fun _ : Fin n =>
      LinearMap.range (Algebra.linearMap (Formalism.L2.Herm.intAf F E) (E ⊗[F] Formalism.L2.Herm.Af F))
    refine Submodule.mem_pi.2 fun i _ => ?_
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (Submodule.mem_pi.1 hx' i (Set.mem_univ i))
    exact LinearMap.mem_range.2 ⟨Formalism.L2.DIV.oToS F E r, congrArg (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) hr⟩
  · intro z hz
    have hz' : z ∈ Submodule.pi Set.univ fun _ : Fin n =>
        LinearMap.range (Algebra.linearMap (Formalism.L2.Herm.intAf F E) (E ⊗[F] Formalism.L2.Herm.Af F)) := hz
    choose y hy using fun i => LinearMap.mem_range.1 (Submodule.mem_pi.1 hz' i (Set.mem_univ i))
    have e : z = ∑ i, y i • (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [Pi.smul_apply, Pi.single_eq_same, map_one]
      rw [← hy j, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (y i) (Submodule.subset_span ⟨Pi.single i 1, ?_, rfl⟩)
    show Pi.single i (1 : E) ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)
    refine Submodule.mem_pi.2 fun j _ => ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact Submodule.zero_mem _

/- English proof (translation)
Rewrite using `[latS_std]`. Simplify using `only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]`. Use `forall_congr' fun i => ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_latS_std (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔
      ∀ i, z i ∈ Formalism.L2.Herm.intAf F E := by
  rw [latS_std]
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_stab_lemma_2 {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (Formalism.L2.Herm.intAf F E) (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)} :
    g ∈ Formalism.UG.stabGL Λ ↔ ∀ z, z ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Λ := Iff.rfl

/- English proof (translation)
Use `show ∑ j, (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * z j ∈ _`. Conclude with `sum_mem fun j _ => mul_mem (SetLike.coe_mem _) (hz j)`.
-/
private theorem intGL_mulVec_lemma (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL F E n y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z) i ∈
      Formalism.L2.Herm.intAf F E := by
  show ∑ j, (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
    E ⊗[F] Formalism.L2.Herm.Af F) * z j ∈ _
  exact sum_mem fun j _ => mul_mem (SetLike.coe_mem _) (hz j)

/- English proof (translation)
Establish `hs : (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := by`. Rewrite using `[mem_latS_std]`. Introduce `k`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `h` using `(mem_latS_std _).1 ((hg _).1 hs) i`. Rewrite `h` using `[Matrix.mulVec_single_one]`. Conclude with `h`.
-/
private theorem col_int_lemma_3 {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hg : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ (g : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have hs : (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := by
    rw [mem_latS_std]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h := (mem_latS_std _).1 ((hg _).1 hs) i
  rw [Matrix.mulVec_single_one] at h
  exact h

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_stab_lemma_2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Establish `e2 : Formalism.L2.DIV.frGL 1 y = Formalism.L2.DIV.intGL F E n y` using `by simp [Formalism.L2.DIV.frGL]`.

Rewrite using `[e2]`. Introduce `z`. Rewrite using `[mem_latS_std, mem_latS_std]`. Prove the components needed by the constructor for the conclusion. Introduce `hz i`.

Conclude with `intGL_mulVec_lemma y z hz i`. Introduce `hz i`. Establish `hz'` using `intGL_mulVec_lemma y⁻¹ _ hz i`. Rewrite `hz'` using `[map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `hg`.

Establish `hg' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ ((g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := mem_stab_lemma_2.1 (in …`. Set `Y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)` to `Matrix.of fun i j => ⟨_, col_int_lemma_3 hg i j⟩`. Set `Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)` to `Matrix.of fun i j => ⟨_, col_int_lemma_3 hg' i j⟩`. Establish `hY : Y.map (Formalism.L2.Herm.intAf F E).subtype = (g : Matrix (Fin n) (Fin n) _)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hY' : Y'.map (Formalism.L2.Herm.intAf F E).subtype = ((g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _)`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `inj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => M.map (Formalism.L2.Herm.intAf F E).subtype` using `Matrix.map_injective Subtype.val_injective`.

Establish `h1 : Y * Y' = 1` using `inj (by show (Y * Y').map _ = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map _`. Rewrite using `[Matrix.map_mul, hY, hY', Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])`. Establish `h2 : Y' * Y = 1` using `inj (by show (Y' * Y).map _ = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map _`. Rewrite using `[Matrix.map_mul, hY, hY', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])`. Use `⟨⟨Y, Y', h1, h2⟩, ?_⟩` and prove the remaining obligations.

Establish `e2 : Formalism.L2.DIV.frGL 1 ⟨Y, Y', h1, h2⟩ = Formalism.L2.DIV.intGL F E n ⟨Y, Y', h1, h2⟩`. Simplify using `[Formalism.L2.DIV.frGL]`. Rewrite using `[e2]`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(show ((Formalism.L2.DIV.intGL F E n ⟨Y, Y', h1, h2⟩ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) = Y.map (Formalism.L2.Herm.intAf F E).subtype from rfl).trans hY`.
-/
theorem St_one : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
    Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
  ext g
  rw [mem_stab_lemma_2]
  constructor
  · rintro ⟨y, rfl⟩
    have e2 : Formalism.L2.DIV.frGL 1 y = Formalism.L2.DIV.intGL F E n y := by simp [Formalism.L2.DIV.frGL]
    rw [e2]
    intro z
    rw [mem_latS_std, mem_latS_std]
    constructor
    · intro hz i
      exact intGL_mulVec_lemma y z hz i
    · intro hz i
      have hz' := intGL_mulVec_lemma y⁻¹ _ hz i
      rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at hz'
  · intro hg
    have hg' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔
        ((g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) :=
      mem_stab_lemma_2.1 (inv_mem (mem_stab_lemma_2.2 hg))
    let Y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := Matrix.of fun i j => ⟨_, col_int_lemma_3 hg i j⟩
    let Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := Matrix.of fun i j => ⟨_, col_int_lemma_3 hg' i j⟩
    have hY : Y.map (Formalism.L2.Herm.intAf F E).subtype = (g : Matrix (Fin n) (Fin n) _) := by
      ext i j
      rfl
    have hY' : Y'.map (Formalism.L2.Herm.intAf F E).subtype =
        ((g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) := by
      ext i j
      rfl
    have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
        M.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
    have h1 : Y * Y' = 1 := inj (by
      show (Y * Y').map _ = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map _
      rw [Matrix.map_mul, hY, hY', Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
    have h2 : Y' * Y = 1 := inj (by
      show (Y' * Y).map _ = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map _
      rw [Matrix.map_mul, hY, hY', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    refine ⟨⟨Y, Y', h1, h2⟩, ?_⟩
    have e2 : Formalism.L2.DIV.frGL 1 ⟨Y, Y', h1, h2⟩ = Formalism.L2.DIV.intGL F E n ⟨Y, Y', h1, h2⟩ := by
      simp [Formalism.L2.DIV.frGL]
    rw [e2]
    apply Units.ext
    exact (show ((Formalism.L2.DIV.intGL F E n ⟨Y, Y', h1, h2⟩ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) _) = Y.map (Formalism.L2.Herm.intAf F E).subtype from rfl).trans hY

/- English proof (translation)
Conclude with `mem_latS_std (F := F) (pullV x v)`.
-/
theorem mem_globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : Fin n → E) :
    v ∈ Formalism.UG.CS.globLat x (stdLat E n) ↔ ∀ i, pullV x v i ∈ Formalism.L2.Herm.intAf F E := by
  exact mem_latS_std (F := F) (pullV x v)

/- English proof (translation)
Unfold `pullV`. Establish `h : (fun j => iA F E ((s • v) j)) = iA F E (algebraMap (𝓞 E) E s) • fun j => iA F E (v j)`. Use function extensionality and compare the values at `j`. Simplify using `[Algebra.smul_def]`. Rewrite using `[h, Matrix.mulVec_smul]`.

Both sides reduce to the same expression.
-/
theorem pullV_osmul (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (s : 𝓞 E) (v : Fin n → E) (i : Fin n) :
    pullV x (s • v) i = iA F E (algebraMap (𝓞 E) E s) * pullV x v i := by
  unfold pullV
  have h : (fun j => iA F E ((s • v) j)) = iA F E (algebraMap (𝓞 E) E s) • fun j => iA F E (v j) := by
    funext j
    simp [Algebra.smul_def]
  rw [h, Matrix.mulVec_smul]
  rfl

/- English proof (translation)
Take `⟨s, hs, hsv⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ Formalism.UG.CS.globLat x (stdLat E n)` from `hv`. Use `⟨s, hs, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← pullV_osmul]`. Conclude with `(mem_globLat x (s • v)).1 hsv j`.
-/
theorem pullV_den {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {P : Pl E} {v : Fin n → E}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ j, iA F E (algebraMap (𝓞 E) E s) * pullV x v j ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ Formalism.UG.CS.globLat x (stdLat E n) := hv
  refine ⟨s, hs, fun j => ?_⟩
  rw [← pullV_osmul]
  exact (mem_globLat x (s • v)).1 hsv j

/- English proof (translation)
Unfold `pullV`. Establish `h : ((Formalism.UG.bc (iA F E) γ)⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) γ⁻¹` using `(map_inv _ _).symm`. Establish `h2 : ((Formalism.UG.bc (iA F E) γ⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (fun i => iA F E (v i)) = fun i => iA F E ((((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) i)`. Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec]`.

Both sides reduce to the same expression. Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, h, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]`.
-/
theorem pullV_rawSm (γ : GL (Fin n) E) (x k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : Fin n → E) :
    pullV (Formalism.UG.bc (iA F E) γ * x * k⁻¹) v =
      (k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ pullV x ((γ⁻¹ : GL (Fin n) E) *ᵥ v) := by
  unfold pullV
  have h : ((Formalism.UG.bc (iA F E) γ)⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) γ⁻¹ :=
    (map_inv _ _).symm
  have h2 : ((Formalism.UG.bc (iA F E) γ⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => iA F E (v i)) =
        fun i => iA F E ((((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) i) := by
    funext i
    rw [RingHom.map_mulVec]
    rfl
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, h, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h2]

end Lat

section Law

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Use `set y := Formalism.L2.DIV.pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨k, hk⟩ with hy`. Establish `e : Formalism.L2.DIV.frGL 1 y = k` using `congrArg Subtype.val ((MonoidHom.ofInjective (Formalism.L2.DIV.frGL_injective (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))).apply_symm_apply ⟨k, hk⟩)`. Establish `e2 : Formalism.L2.DIV.frGL 1 y = Formalism.L2.DIV.intGL F E n y` using `by simp [Formalism.L2.DIV.frGL]`. Establish `e3 : k = Formalism.L2.DIV.intGL F E n y` using `e.symm.trans e2`. Use `⟨y, fun i j => ?_, fun P i j => rfl⟩` and prove the remaining obligations.

Conclude with `congrArg (fun g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) e3`.
-/
theorem St_one_int {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), (∀ i j, (k : Matrix (Fin n) (Fin n) _) i j = (y i j : E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      ∀ P : Pl E, ∀ i j, ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨k, hk⟩ : GL (Fin n) (kP P)) :
        Matrix (Fin n) (Fin n) (kP P)) i j = resS F P (y i j) := by
  set y := Formalism.L2.DIV.pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨k, hk⟩ with hy
  have e : Formalism.L2.DIV.frGL 1 y = k :=
    congrArg Subtype.val ((MonoidHom.ofInjective
      (Formalism.L2.DIV.frGL_injective (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))).apply_symm_apply ⟨k, hk⟩)
  have e2 : Formalism.L2.DIV.frGL 1 y = Formalism.L2.DIV.intGL F E n y := by simp [Formalism.L2.DIV.frGL]
  have e3 : k = Formalism.L2.DIV.intGL F E n y := e.symm.trans e2
  refine ⟨y, fun i j => ?_, fun P i j => rfl⟩
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) e3

/- English proof (translation)
Use `show ∑ j, (k : Matrix (Fin n) (Fin n) _) i j * u j = _`. Simplify using `only [hy]`.
-/
theorem mulVec_int_apply {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)}
    (hy : ∀ i j, (k : Matrix (Fin n) (Fin n) _) i j = (y i j : E ⊗[F] Formalism.L2.Herm.Af F))
    (u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) _) *ᵥ u) i = ∑ j, (y i j : E ⊗[F] Formalism.L2.Herm.Af F) * u j := by
  show ∑ j, (k : Matrix (Fin n) (Fin n) _) i j * u j = _
  simp only [hy]

/- English proof (translation)
Take `⟨y, hy, hred⟩` from `St_one_int hg`. Rewrite using `[mulVec_int_apply hy u i, redA_sum P hs u hu (fun j => (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j)]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hred P i j]`.
-/
private theorem redA_mulVec_lemma_4 {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (P : Pl E) {s : 𝓞 E} (hs : s ∉ P.asIdeal) (u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hu : ∀ j, iA F E (algebraMap (𝓞 E) E s) * u j ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    redA P (((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ u) i) =
      ∑ j, ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨g, hg⟩ : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) i j *
        redA P (u j) := by
  obtain ⟨y, hy, hred⟩ := St_one_int hg
  rw [mulVec_int_apply hy u i,
    redA_sum P hs u hu (fun j => (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j)]
  exact Finset.sum_congr rfl fun j _ => by rw [hred P i j]

/- English proof (translation)
Establish `hkSt : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `congruence_subgroup_le_stabilizer hc n ST k.2`. Use `set g := ((ratHom hc n γ : UF E n) : Sp E n ≃ₗ[E] Sp E n) with hg`. Establish `hsymm : ∀ v : Fin n → E, g.symm v = (((γ : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v` using `fun v => rfl`. Establish `hpull : ∀ v, pullV (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) v = ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ pullV x (g.symm v)` using `fun v => by`. Rewrite using `[hsymm]`.

Conclude with `pullV_rawSm _ x _ v`. Establish `hmemg : ∀ (L : Submodule (𝓞 E) (Sp E n)) v, v ∈ Formalism.HermitianLatticesTheory.gmap g L ↔ g.symm v ∈ L`. Introduce `L v`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Introduce `h`. Conclude with `⟨g.symm v, h, by simp⟩`.

Establish `hloc : ∀ (P : Pl E) (L : Submodule (𝓞 E) (Sp E n)) v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g L) ↔ g.symm v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L`. Introduce `P L v`. Use `show (∃ s ∈ P.asIdeal.primeCompl, s • v ∈ Formalism.HermitianLatticesTheory.gmap g L) ↔ ∃ s ∈ P.asIdeal.primeCompl, s • g.symm v ∈ L`. Establish `hs : ∀ (s : 𝓞 E) (w : Sp E n), g.symm (s • w) = s • g.symm w` using `fun s w => by`. Rewrite using `[← algebraMap_smul E s w, map_smul, algebraMap_smul]`.

Simplify using `only [hmemg, hs]`. Establish `hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E …`. Establish `h5` using `hkSt`. Rewrite `h5` using `[St_one]`. Conclude with `h5`.

Establish `e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔ pullV y v ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm`. Establish `hN : Formalism.UG.CS.globLat (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) (stdLat E n) = Formalism.HermitianLatticesTheory.gmap g (Formalism.UG.CS.globLat x (stdLat E n))`. Use extensionality with `v`. Rewrite using `[hmemg, e, e, hpull]`. Conclude with `(hk' (pullV x (g.symm v))).symm`.

Unfold `decoRaw Deco.act`. Use `congr 1`. Use `case e_f =>`. Use function extensionality and compare the values at `P v`. Simplify using `only`.

Rewrite using `[hN, hloc]`. Use `split_ifs with hv`. Take `⟨s, hs, hsv⟩` from `pullV_den hv`. Establish `hmi : redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P.1 ⟨_, hkSt⟩ ∈ mirab (kP P.1) n`. Establish `hJ' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ UAd hc n ⊓ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⊓ ⨅ P ∈ ST, mirAt (F` using `F) n P := k.2`.

Establish `h3` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hJ').2 P.1) P.2`. Take `⟨s', hs'', hsk⟩` from `Subgroup.mem_map.1 h3`. Establish `hs' : s' = ⟨_, hkSt⟩` using `Subtype.ext hsk`. Rewrite using `[← hs']`. Conclude with `hs''`.

Rewrite using `[hpull, redA_mulVec_lemma_4 hkSt P.1 hs _ hsv, Finset.sum_eq_single (lastIdx n) (fun j _ hj => by rw [hmi j, if_neg hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h), hmi (lastIdx n), if_pos rfl, one_mul]`. Both sides reduce to the same expression. Use `case e_be =>`. Use function extensionality and compare the values at `w v`. Simplify using `only`.

Rewrite using `[hN, hloc]`. Use `split_ifs with hv`. Use function extensionality and compare the values at `i`. Take `⟨s, hs, hsv⟩` from `pullV_den hv`. Rewrite using `[hpull, redA_mulVec_lemma_4 hkSt w.1 hs _ hsv]`.

Both sides reduce to the same expression. Conclude with `(Matrix.mulVec_zero _).symm`.
-/
theorem decoRaw_rawSm (γ : URat hc n) (k : J0 hc n ST) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    decoRaw ST SG (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) =
      (decoRaw ST SG x).act ((ratHom hc n γ : UF E n) : Sp E n ≃ₗ[E] Sp E n) (redG hc n ST SG k) := by
  have hkSt : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := congruence_subgroup_le_stabilizer hc n ST k.2
  set g := ((ratHom hc n γ : UF E n) : Sp E n ≃ₗ[E] Sp E n) with hg
  have hsymm : ∀ v : Fin n → E, g.symm v = (((γ : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v :=
    fun v => rfl
  have hpull : ∀ v, pullV (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) v =
      ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ pullV x (g.symm v) := fun v => by
    rw [hsymm]
    exact pullV_rawSm _ x _ v
  have hmemg : ∀ (L : Submodule (𝓞 E) (Sp E n)) v, v ∈ Formalism.HermitianLatticesTheory.gmap g L ↔ g.symm v ∈ L := by
    intro L v
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro h
      exact ⟨g.symm v, h, by simp⟩
  have hloc : ∀ (P : Pl E) (L : Submodule (𝓞 E) (Sp E n)) v,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g L) ↔ g.symm v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L := by
    intro P L v
    show (∃ s ∈ P.asIdeal.primeCompl, s • v ∈ Formalism.HermitianLatticesTheory.gmap g L) ↔
      ∃ s ∈ P.asIdeal.primeCompl, s • g.symm v ∈ L
    have hs : ∀ (s : 𝓞 E) (w : Sp E n), g.symm (s • w) = s • g.symm w := fun s w => by
      rw [← algebraMap_smul E s w, map_smul, algebraMap_smul]
    simp only [hmemg, hs]
  have hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔
      ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := by
    have h5 := hkSt
    rw [St_one] at h5
    exact h5
  have e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔ pullV y v ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) :=
    fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm
  have hN : Formalism.UG.CS.globLat (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) (stdLat E n) = Formalism.HermitianLatticesTheory.gmap g (Formalism.UG.CS.globLat x (stdLat E n)) := by
    ext v
    rw [hmemg, e, e, hpull]
    exact (hk' (pullV x (g.symm v))).symm
  unfold decoRaw Deco.act
  congr 1
  case e_f =>
    funext P v
    dsimp only
    rw [hN, hloc]
    split_ifs with hv
    · obtain ⟨s, hs, hsv⟩ := pullV_den hv
      have hmi : redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P.1 ⟨_, hkSt⟩ ∈ mirab (kP P.1) n := by
        have hJ' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈
            UAd hc n ⊓ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⊓ ⨅ P ∈ ST, mirAt (F := F) n P := k.2
        have h3 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hJ').2 P.1) P.2
        obtain ⟨s', hs'', hsk⟩ := Subgroup.mem_map.1 h3
        have hs' : s' = ⟨_, hkSt⟩ := Subtype.ext hsk
        rw [← hs']
        exact hs''
      rw [hpull, redA_mulVec_lemma_4 hkSt P.1 hs _ hsv,
        Finset.sum_eq_single (lastIdx n) (fun j _ hj => by rw [hmi j, if_neg hj, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), hmi (lastIdx n), if_pos rfl, one_mul]
    · rfl
  case e_be =>
    funext w v
    dsimp only
    rw [hN, hloc]
    split_ifs with hv
    · funext i
      obtain ⟨s, hs, hsv⟩ := pullV_den hv
      rw [hpull, redA_mulVec_lemma_4 hkSt w.1 hs _ hsv]
      rfl
    · exact (Matrix.mulVec_zero _).symm

end Law

section Pt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Take `⟨k, hk1, rfl⟩` from `hm`. Use `show decoRaw ST SG (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoRaw ST SG x`. Establish `hSt : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `congruence_subgroup_le_stabilizer hc n ST k.2`. Establish `hSt' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `inv_mem hSt`. Establish `hredinv : ∀ P : Pl E, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt'⟩ = (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt⟩)⁻¹` using `fun P => map_inv (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P) ⟨_, hSt⟩`.

Establish `hmir : ∀ P ∈ ST, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt⟩ ∈ mirab (kP P) n`. Introduce `P hP`. Establish `hJ' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ UAd hc n ⊓ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⊓ ⨅ P ∈ ST, mirAt (F` using `F) n P := k.2`. Establish `h3` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hJ').2 P) hP`. Take `⟨s, hs, hsk⟩` from `Subgroup.mem_map.1 h3`.

Establish `hs' : s = ⟨_, hSt⟩` using `Subtype.ext hsk`. Rewrite using `[← hs']`. Conclude with `hs`. Establish `hid : ∀ w : SG, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨_, hSt⟩ = 1` using `fun w => congrFun (MonoidHom.mem_ker.1 hk1) w`. Establish `hpull : ∀ v, pullV (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) v = (((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ pullV x v` using `fun v => by`.

Unfold `pullV`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]`. Establish `hN : Formalism.UG.CS.globLat (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n) = Formalism.UG.CS.globLat x (stdLat E n)`. Establish `hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ (((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.He …`. Establish `h5` using `hSt'`.

Rewrite `h5` using `[St_one]`. Conclude with `h5`. Establish `e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔ pullV y v ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm`. Use extensionality with `v`. Rewrite using `[e, e, hpull]`.

Conclude with `(hk' (pullV x v)).symm`. Unfold `decoRaw`. Rewrite using `[hN]`. Use `congr 1`. Use function extensionality and compare the values at `P v split_ifs with hv`.

Take `⟨s, hs, hsv⟩` from `pullV_den hv`. Establish `hmi` using `inv_mem (hmir P.1 P.2)`. Rewrite using `[hpull, redA_mulVec_lemma_4 hSt' P.1 hs _ hsv, hredinv, Finset.sum_eq_single (lastIdx n) (fun j _ hj => by rw [hmi j, if_neg hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h), hmi (lastIdx n), if_pos rfl, one_mul]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `w v split_ifs with hv`.

Use function extensionality and compare the values at `i`. Take `⟨s, hs, hsv⟩` from `pullV_den hv`. Rewrite using `[hpull, redA_mulVec_lemma_4 hSt' w.1 hs _ hsv, hredinv, hid w, inv_one]`. Simplify using `[Matrix.one_apply]`. Both sides reduce to the same expression.
-/
theorem decorated_lattice_mul_principal (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {m : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hm : m ∈ K1 hc n ST SG) : decoRaw ST SG (x * m) = decoRaw ST SG x := by
  obtain ⟨k, hk1, rfl⟩ := hm
  show decoRaw ST SG (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoRaw ST SG x
  have hSt : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := congruence_subgroup_le_stabilizer hc n ST k.2
  have hSt' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := inv_mem hSt
  have hredinv : ∀ P : Pl E, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt'⟩ = (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt⟩)⁻¹ :=
    fun P => map_inv (redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P) ⟨_, hSt⟩
  have hmir : ∀ P ∈ ST, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨_, hSt⟩ ∈ mirab (kP P) n := by
    intro P hP
    have hJ' : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈
        UAd hc n ⊓ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⊓ ⨅ P ∈ ST, mirAt (F := F) n P := k.2
    have h3 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hJ').2 P) hP
    obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.1 h3
    have hs' : s = ⟨_, hSt⟩ := Subtype.ext hsk
    rw [← hs']
    exact hs
  have hid : ∀ w : SG, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨_, hSt⟩ = 1 := fun w => congrFun (MonoidHom.mem_ker.1 hk1) w
  have hpull : ∀ v, pullV (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) v =
      (((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ pullV x v := fun v => by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
  have hN : Formalism.UG.CS.globLat (x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (stdLat E n) = Formalism.UG.CS.globLat x (stdLat E n) := by
    have hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔
        (((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := by
      have h5 := hSt'
      rw [St_one] at h5
      exact h5
    have e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔ pullV y v ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) :=
      fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm
    ext v
    rw [e, e, hpull]
    exact (hk' (pullV x v)).symm
  unfold decoRaw
  rw [hN]
  congr 1
  · funext P v
    split_ifs with hv
    · obtain ⟨s, hs, hsv⟩ := pullV_den hv
      have hmi := inv_mem (hmir P.1 P.2)
      rw [hpull, redA_mulVec_lemma_4 hSt' P.1 hs _ hsv, hredinv,
        Finset.sum_eq_single (lastIdx n) (fun j _ hj => by rw [hmi j, if_neg hj, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), hmi (lastIdx n), if_pos rfl, one_mul]
    · rfl
  · funext w v
    split_ifs with hv
    · funext i
      obtain ⟨s, hs, hsv⟩ := pullV_den hv
      rw [hpull, redA_mulVec_lemma_4 hSt' w.1 hs _ hsv, hredinv, hid w, inv_one]
      simp [Matrix.one_apply]
    · rfl

/- English proof (translation)
Unfold `decoOf`. Rewrite using `[decorated_lattice_mul_principal hc n ST SG x hm]`.
-/
theorem decoration_mul_principal (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {m : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hm : m ∈ K1 hc n ST SG) : decoOf ST SG (x * m) = decoOf ST SG x := by
  unfold decoOf
  rw [decorated_lattice_mul_principal hc n ST SG x hm]

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul ((K1 hc n ST SG).subgroupOf (UAd hc n)) x`. Unfold `decoPt`. Rewrite using `[hk, Subgroup.coe_mul]`. Conclude with `decoration_mul_principal hc n ST SG _ (Subgroup.mem_subgroupOf.1 k.2)`.
-/
theorem decoPt_mk (x : UAd hc n) :
    decoPt hc n ST SG (x : adPt hc n ST SG) = decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((K1 hc n ST SG).subgroupOf (UAd hc n)) x
  unfold decoPt
  rw [hk, Subgroup.coe_mul]
  exact decoration_mul_principal hc n ST SG _ (Subgroup.mem_subgroupOf.1 k.2)

variable (H : Subgroup (GLG E n SG))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rawSm_val (γ : URat hc n) (k : J0 hc n ST) (x : UAd hc n) :
    ((rawSm hc n ST γ k x : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * x * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := rfl

/- English proof (translation)
Introduce `g q`. Take `⟨γ, kq⟩` from `g`. Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective kq`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective q`. Use `show decoPt hc n ST SG ((rawSm hc n ST γ k.1 x : UAd hc n) : adPt hc n ST SG) = _`.

Rewrite using `[decoPt_mk, decoPt_mk, rawSm_val]`. Establish `hx` using `hOk _ x.2`. Establish `hr` using `hOk _ (rawSm hc n ST γ k.1 x).2`. Rewrite `hr` using `[rawSm_val]`. Unfold `decoOf`.

Rewrite using `[dif_pos hr, dif_pos hx]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show decoRaw ST SG _ = _`. Rewrite using `[decoRaw_rawSm]`. Both sides reduce to the same expression.
-/
theorem decoPtEqv_of (hOk : DecoOfOk hc n ST SG) : DecoPtEqv hc n ST SG H := by
  intro g q
  obtain ⟨γ, kq⟩ := g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  show decoPt hc n ST SG ((rawSm hc n ST γ k.1 x : UAd hc n) : adPt hc n ST SG) = _
  rw [decoPt_mk, decoPt_mk, rawSm_val]
  have hx := hOk _ x.2
  have hr := hOk _ (rawSm hc n ST γ k.1 x).2
  rw [rawSm_val] at hr
  unfold decoOf
  rw [dif_pos hr, dif_pos hx]
  apply Subtype.ext
  show decoRaw ST SG _ = _
  rw [decoRaw_rawSm]
  rfl

end Pt

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
The claim follows from `Formalism.UG.P.global_lattice_one_holds F E (Fin n) (stdLat E n) (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top`.
-/
theorem globLat_one_std : Formalism.UG.CS.globLat (F := F) (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n) = stdLat E n :=
  Formalism.UG.P.global_lattice_one_holds F E (Fin n) (stdLat E n) (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg)
    (stdLat_lattice (E := E) (n := n)).span_eq_top

/- English proof (translation)
Simplify using `[pullV]`.
-/
theorem pullV_one (v : Fin n → E) : pullV (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) v = fun i => iA F E (v i) := by
  simp [pullV]

/- English proof (translation)
Take `⟨s, hs, hsv⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ stdLat E n` from `hv`. Establish `hsv' : s • v ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)` using `hsv`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 (Submodule.mem_pi.1 hsv' i (Set.mem_univ i))`. Rewrite using `[pullV_one]`. Conclude with `redA_iA P hs (by rw [hr, Pi.smul_apply, Algebra.smul_def])`.
-/
theorem redA_pullV_one {P : Pl E} {v : Fin n → E} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)) (i : Fin n) :
    redA P (pullV (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) v i) = redP P (v i) := by
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • v ∈ stdLat E n := hv
  have hsv' : s • v ∈ Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) := hsv
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (Submodule.mem_pi.1 hsv' i (Set.mem_univ i))
  rw [pullV_one]
  exact redA_iA P hs (by rw [hr, Pi.smul_apply, Algebra.smul_def])

/- English proof (translation)
Unfold `decoRaw Deco.base`. Rewrite using `[globLat_one_std]`. Use `congr 1`. Use function extensionality and compare the values at `P x split_ifs with hx`. Conclude with `redA_pullV_one hx _`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `w x split_ifs with hx`. Use function extensionality and compare the values at `i`. Conclude with `redA_pullV_one hx i`. Both sides reduce to the same expression.
-/
theorem decoRaw_one : decoRaw ST SG (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Deco.base E n ST SG := by
  unfold decoRaw Deco.base
  rw [globLat_one_std]
  congr 1
  · funext P x
    split_ifs with hx
    · exact redA_pullV_one hx _
    · rfl
  · funext w x
    split_ifs with hx
    · funext i
      exact redA_pullV_one hx i
    · rfl

/- English proof (translation)
Unfold `decoOf`. Rewrite using `[decoRaw_one]`. Conclude with `dif_pos Deco.base_ok`.
-/
theorem decoOf_one : decoOf ST SG (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = DecoSet.base E n ST SG := by
  unfold decoOf
  rw [decoRaw_one]
  exact dif_pos Deco.base_ok

end Base

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {n : ℕ}

def pullVAdd (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : (Fin n → E) →+ (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) where
  toFun := pullV x
  map_zero' := by
    unfold pullV
    have : (fun i : Fin n => iA F E ((0 : Fin n → E) i)) = 0 := by funext i; simp
    rw [this, Matrix.mulVec_zero]
  map_add' v w := by
    unfold pullV
    have : (fun i : Fin n => iA F E ((v + w) i)) = (fun i => iA F E (v i)) + fun i => iA F E (w i) := by
      funext i; simp
    rw [this, Matrix.mulVec_add]

/- English proof (translation)
Establish `hs1 : (1 : 𝓞 E) ∉ P.asIdeal` using `fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hm : iA F E (algebraMap (𝓞 E) E 1) * iA F E (algebraMap (𝓞 E) E r) ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[map_one, map_one, one_mul]`. Conclude with `iA_mem r`. Apply `redA_eq P hs1 hm` to reduce the goal to its premises.

Rewrite using `[map_one, one_mul, ← Formalism.L2.DIV.resS_oToS (F := F) P r]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subtype.coe_mk, map_one, one_mul, ← iA_coe]`.
-/
theorem redA_coe (P : Pl E) (r : 𝓞 E) : redA P (iA F E (algebraMap (𝓞 E) E r)) = Ideal.Quotient.mk P.asIdeal r := by
  have hs1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hm : iA F E (algebraMap (𝓞 E) E 1) * iA F E (algebraMap (𝓞 E) E r) ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_one, map_one, one_mul]
    exact iA_mem r
  apply redA_eq P hs1 hm
  rw [map_one, one_mul, ← Formalism.L2.DIV.resS_oToS (F := F) P r]
  congr 1
  apply Subtype.ext
  simp only [Subtype.coe_mk, map_one, one_mul, ← iA_coe]

/- English proof (translation)
Use `choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)`. Use `set u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F := (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ fun i => iA F E (algebraMap (𝓞 E) E (a i)) with hudef`. Establish `hxu : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ u = fun i => iA F E (algebraMap (𝓞 E) E (a i))`. Rewrite using `[hudef, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hu : u ∈ Submodule.span (Formalism.L2.Herm.intAf F E) ((fun v : Fin n → E => fun i => iA F E (v i)) '' (Formalism.UG.CS.globLat x (stdLat E n) : Set (Fin n → E)))`.

Rewrite using `[Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x u]`. Rewrite using `[mem_latS_std, hxu]`. Introduce `i`. Conclude with `iA_mem (a i)`. Take `⟨m, f, g, hfg⟩` from `Submodule.mem_span_set'.1 hu`.

Use `choose v hv hvg using fun l => (g l).2`. Use `choose b hb using fun l => Ideal.Quotient.mk_surjective (resS F P (f l))`. Establish `hint : ∀ l j, pullV x (v l) j ∈ Formalism.L2.Herm.intAf F E` using `fun l => (mem_globLat x _).1 (hv l)`. Establish `hint1 : ∀ l j, iA F E (algebraMap (𝓞 E) E 1) * pullV x (v l) j ∈ Formalism.L2.Herm.intAf F E`. Introduce `l j`.

Rewrite using `[map_one, map_one, one_mul]`. Conclude with `hint l j`. Establish `key : ∀ i, iA F E (algebraMap (𝓞 E) E (a i)) = ∑ l, (f l : E ⊗[F] Formalism.L2.Herm.Af F) * pullV x (v l) i`. Introduce `i`. Establish `h1` using `congrFun hxu i`.

Rewrite `h1` using `[← hfg, Matrix.mulVec_sum, Finset.sum_apply]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← hvg l]`. Use `show (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ ((f l : E ⊗[F] Formalism.L2.Herm.Af F) • fun j => iA F E (v l j))) i = _`.

Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression. Use `⟨∑ l, b l • v l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hv l), fun i => ?_⟩` and prove the remaining obligations. Establish `hsum : pullV x (∑ l, b l • v l) i = ∑ l, ((Formalism.L2.DIV.oToS F E (b l) : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * pullV x (v l) i`. Use `map_sum (pullVAdd x) (fun l => b l • v l) Finset.univ` as an intermediate fact.

Establish `h2` using `congrFun this i`. Simplify using `only [pullVAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply] at h2`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[pullV_osmul]`.

Both sides reduce to the same expression. Rewrite using `[hsum, redA_sum P (one_notMem P) _ (hint1 · i), ← ha i, ← redA_coe (F := F) P (a i), key i, redA_sum P (one_notMem P) _ (hint1 · i) f]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.DIV.resS_oToS, hb]`.
-/
theorem redN_surj (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (P : Pl E) (c : Fin n → kP P) :
    ∃ v ∈ Formalism.UG.CS.globLat x (stdLat E n), ∀ i, redA P (pullV x v i) = c i := by
  classical
  choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)
  set u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ fun i => iA F E (algebraMap (𝓞 E) E (a i)) with hudef
  have hxu : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ u =
      fun i => iA F E (algebraMap (𝓞 E) E (a i)) := by
    rw [hudef, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hu : u ∈ Submodule.span (Formalism.L2.Herm.intAf F E)
      ((fun v : Fin n → E => fun i => iA F E (v i)) '' (Formalism.UG.CS.globLat x (stdLat E n) : Set (Fin n → E))) := by
    rw [Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
      (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x u]
    rw [mem_latS_std, hxu]
    intro i; exact iA_mem (a i)
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hu
  choose v hv hvg using fun l => (g l).2
  choose b hb using fun l => Ideal.Quotient.mk_surjective (resS F P (f l))
  have hint : ∀ l j, pullV x (v l) j ∈ Formalism.L2.Herm.intAf F E := fun l => (mem_globLat x _).1 (hv l)
  have hint1 : ∀ l j, iA F E (algebraMap (𝓞 E) E 1) * pullV x (v l) j ∈ Formalism.L2.Herm.intAf F E := by
    intro l j; rw [map_one, map_one, one_mul]; exact hint l j
  have key : ∀ i, iA F E (algebraMap (𝓞 E) E (a i)) = ∑ l, (f l : E ⊗[F] Formalism.L2.Herm.Af F) * pullV x (v l) i := by
    intro i
    have h1 := congrFun hxu i
    rw [← hfg, Matrix.mulVec_sum, Finset.sum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hvg l]
    show (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      ((f l : E ⊗[F] Formalism.L2.Herm.Af F) • fun j => iA F E (v l j))) i = _
    rw [Matrix.mulVec_smul]
    rfl
  refine ⟨∑ l, b l • v l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hv l), fun i => ?_⟩
  have hsum : pullV x (∑ l, b l • v l) i =
      ∑ l, ((Formalism.L2.DIV.oToS F E (b l) : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * pullV x (v l) i := by
    have := map_sum (pullVAdd x) (fun l => b l • v l) Finset.univ
    have h2 := congrFun this i
    simp only [pullVAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pullV_osmul]
    rfl
  rw [hsum, redA_sum P (one_notMem P) _ (hint1 · i), ← ha i, ← redA_coe (F := F) P (a i), key i,
    redA_sum P (one_notMem P) _ (hint1 · i) f]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Formalism.L2.DIV.resS_oToS, hb]

end Surj

section Inj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Introduce `j`. Take `⟨v, hv, hc⟩` from `redN_surj y P (Pi.single j 1)`. Establish `h1` using `h v hv`. Simplify using `only [hc] at h1`. Simplify `h1` using `[Pi.single_apply]`.
-/
theorem red_row_eq (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {P : Pl E} {A B : Matrix (Fin n) (Fin n) (kP P)} (i : Fin n)
    (h : ∀ v ∈ Formalism.UG.CS.globLat y (stdLat E n),
      ∑ j, A i j * redA P (pullV y v j) = ∑ j, B i j * redA P (pullV y v j)) :
    ∀ j, A i j = B i j := by
  intro j
  classical
  obtain ⟨v, hv, hc⟩ := redN_surj y P (Pi.single j 1)
  have h1 := h v hv
  simp only [hc] at h1
  simpa [Pi.single_apply] using h1

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Deco.act, Formalism.HermitianLatticesTheory.gmap]`.
-/
theorem Deco.act_one_N (d : Deco E n ST SG) (g : GLG E n SG) : (d.act 1 g).N = d.N := by
  ext x
  simp [Deco.act, Formalism.HermitianLatticesTheory.gmap]

/- English proof (translation)
Establish `hN : Formalism.UG.CS.globLat x (stdLat E n) = Formalism.UG.CS.globLat y (stdLat E n)` using `(congrArg Deco.N h).trans (Deco.act_one_N ST SG _ g)`. Establish `hfin` using `Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg`. Establish `hspan` using `(stdLat_lattice (E := E) (n := n)).span_eq_top`. Establish `hSR` using `Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan`. Establish `hkS : x⁻¹ * y ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))`.

Rewrite using `[St_one]`. Introduce `z`. Establish `e1` using `hSR y ((y : Matrix (Fin n) (Fin n) _) *ᵥ z)`. Establish `e2` using `hSR x ((y : Matrix (Fin n) (Fin n) _) *ᵥ z)`. Establish `hyy : ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ ((y : Matrix (Fin n) (Fin n) _) *ᵥ z) = z`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hxy : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ ((y : Matrix (Fin n) (Fin n) _) *ᵥ z) = ((x⁻¹ * y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul]`. Rewrite `e1` using `[← hN, e2, hxy, hyy]`. Conclude with `e1.symm`.

Establish `hkU : x⁻¹ * y ∈ UAd hc n` using `Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy`. Take `⟨z, hzk, hzr⟩` from `St_one_int hkS`. Establish `hpx : ∀ v, pullV x v = ((x⁻¹ * y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ pullV y v`. Introduce `v`. Unfold `pullV`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]`. Establish `hval : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat y (stdLat E n) → ∀ i, redA P (pullV x v i) = ∑ j, resS F P (z i j) * redA P (pullV y v j)`. Introduce `P v hv i`. Establish `hint : ∀ j, iA F E (algebraMap (𝓞 E) E 1) * pullV y v j ∈ Formalism.L2.Herm.intAf F E`. Introduce `j`.

Rewrite using `[map_one, map_one, one_mul]`. Conclude with `(mem_globLat y v).1 hv j`. Rewrite using `[hpx, mulVec_int_apply hzk]`. Conclude with `redA_sum P (one_notMem P) _ hint _`. Establish `hinP : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat y (stdLat E n) → v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ∧ v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat y (std …` using `fun P v hv => ⟨le_locP P _ (hN ▸ hv), le_locP P _ hv⟩`.

Establish `hone : ∀ v : Fin n → E, (1 : Sp E n ≃ₗ[E] Sp E n).symm v = v` using `fun _ => rfl`. Establish `hbe : ∀ w : SG, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨_, hkS⟩ = g w`. Introduce `w`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Rewrite using `[hzr w.1 i j]`. Use `red_row_eq y (A := (Formalism.UG.bc (resS F w.1) z : GL (Fin n) (kP w.1)).1) (B := (g w).1) i (fun v hv => ?_) j` and prove the remaining obligations. Establish `hb` using `congrFun (congrFun (congrArg Deco.be h) w) v`. Simplify using `only [decoRaw, Deco.act, hone, if_pos (hinP w.1 v hv).1, if_pos (hinP w.1 v hv).2] at hb`. Establish `hb'` using `congrFun hb i`.

Rewrite `hb'` using `[hval w.1 v hv i]`. Conclude with `hb'`. Establish `hf : ∀ P : ST, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P.1 ⟨_, hkS⟩ ∈ mirab (kP P.1) n`. Introduce `P j`. Rewrite using `[hzr P.1 (lastIdx n) j]`.

Use `red_row_eq y (A := (Formalism.UG.bc (resS F P.1) z : GL (Fin n) (kP P.1)).1) (B := (1 : Matrix (Fin n) (Fin n) (kP P.1))) (lastIdx n) (fun v hv => ?_) j |>.trans ?_` and prove the remaining obligations. Establish `hb` using `congrFun (congrFun (congrArg Deco.f h) P) v`. Simplify using `only [decoRaw, Deco.act, hone, if_pos (hinP P.1 v hv).1, if_pos (hinP P.1 v hv).2] at hb`. Rewrite `hb` using `[hval P.1 v hv (lastIdx n)]`. Rewrite using `[show ∑ j, (1 : Matrix (Fin n) (Fin n) (kP P.1)) (lastIdx n) j * redA P.1 (pullV y v j) = redA P.1 (pullV y v (lastIdx n)) by simp [Matrix.one_apply]]`.

Conclude with `hb`. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `hij : lastIdx n = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hij, Ne.symm hij]`. Establish `hJ : x⁻¹ * y ∈ J0 hc n ST` using `⟨⟨hkU, hkS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ⟨⟨_, hkS⟩, hf ⟨P, hP⟩, rfl⟩⟩`. Conclude with `⟨hJ, funext hbe⟩`.
-/
theorem mem_congruence_of_action {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) (hy : y ∈ UAd hc n)
    (g : GLG E n SG) (h : decoRaw ST SG x = (decoRaw ST SG y).act 1 g) :
    ∃ hJ : x⁻¹ * y ∈ J0 hc n ST, redG hc n ST SG ⟨_, hJ⟩ = g := by
  classical
  have hN : Formalism.UG.CS.globLat x (stdLat E n) = Formalism.UG.CS.globLat y (stdLat E n) :=
    (congrArg Deco.N h).trans (Deco.act_one_N ST SG _ g)
  have hfin := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg
  have hspan := (stdLat_lattice (E := E) (n := n)).span_eq_top
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan
  have hkS : x⁻¹ * y ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [St_one]
    intro z
    have e1 := hSR y ((y : Matrix (Fin n) (Fin n) _) *ᵥ z)
    have e2 := hSR x ((y : Matrix (Fin n) (Fin n) _) *ᵥ z)
    have hyy : ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        ((y : Matrix (Fin n) (Fin n) _) *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hxy : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        ((y : Matrix (Fin n) (Fin n) _) *ᵥ z) = ((x⁻¹ * y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    rw [← hN, e2, hxy, hyy] at e1
    exact e1.symm
  have hkU : x⁻¹ * y ∈ UAd hc n := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  obtain ⟨z, hzk, hzr⟩ := St_one_int hkS
  have hpx : ∀ v, pullV x v = ((x⁻¹ * y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ pullV y v := by
    intro v
    unfold pullV
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hval : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat y (stdLat E n) → ∀ i,
      redA P (pullV x v i) = ∑ j, resS F P (z i j) * redA P (pullV y v j) := by
    intro P v hv i
    have hint : ∀ j, iA F E (algebraMap (𝓞 E) E 1) * pullV y v j ∈ Formalism.L2.Herm.intAf F E := by
      intro j; rw [map_one, map_one, one_mul]; exact (mem_globLat y v).1 hv j
    rw [hpx, mulVec_int_apply hzk]
    exact redA_sum P (one_notMem P) _ hint _
  have hinP : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat y (stdLat E n) →
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ∧
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := fun P v hv =>
    ⟨le_locP P _ (hN ▸ hv), le_locP P _ hv⟩
  have hone : ∀ v : Fin n → E, (1 : Sp E n ≃ₗ[E] Sp E n).symm v = v := fun _ => rfl
  have hbe : ∀ w : SG, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨_, hkS⟩ = g w := by
    intro w
    apply Units.ext
    ext i j
    rw [hzr w.1 i j]
    refine red_row_eq y (A := (Formalism.UG.bc (resS F w.1) z : GL (Fin n) (kP w.1)).1) (B := (g w).1) i (fun v hv => ?_) j
    have hb := congrFun (congrFun (congrArg Deco.be h) w) v
    simp only [decoRaw, Deco.act, hone, if_pos (hinP w.1 v hv).1, if_pos (hinP w.1 v hv).2] at hb
    have hb' := congrFun hb i
    rw [hval w.1 v hv i] at hb'
    exact hb'
  have hf : ∀ P : ST, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P.1 ⟨_, hkS⟩ ∈ mirab (kP P.1) n := by
    intro P j
    rw [hzr P.1 (lastIdx n) j]
    refine red_row_eq y (A := (Formalism.UG.bc (resS F P.1) z : GL (Fin n) (kP P.1)).1)
      (B := (1 : Matrix (Fin n) (Fin n) (kP P.1))) (lastIdx n) (fun v hv => ?_) j |>.trans ?_
    · have hb := congrFun (congrFun (congrArg Deco.f h) P) v
      simp only [decoRaw, Deco.act, hone, if_pos (hinP P.1 v hv).1, if_pos (hinP P.1 v hv).2] at hb
      rw [hval P.1 v hv (lastIdx n)] at hb
      rw [show ∑ j, (1 : Matrix (Fin n) (Fin n) (kP P.1)) (lastIdx n) j * redA P.1 (pullV y v j) =
        redA P.1 (pullV y v (lastIdx n)) by simp [Matrix.one_apply]]
      exact hb
    · rw [Matrix.one_apply]
      by_cases hij : lastIdx n = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
  have hJ : x⁻¹ * y ∈ J0 hc n ST :=
    ⟨⟨hkU, hkS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ⟨⟨_, hkS⟩, hf ⟨P, hP⟩, rfl⟩⟩
  exact ⟨hJ, funext hbe⟩

end Inj

section Inj2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Establish `hact : ∀ d : Deco E n ST SG, d.act 1 1 = d`. Introduce and unpack `⟨N, f, be⟩`. Unfold `Deco.act`. Use `congr 1`. Apply the tactic sequence `all_goals first`.

Consider the case `exact Deco.act_one_N ST SG ⟨N, f, be⟩ 1`. Consider the case `rfl`. Consider the case `(funext w z; simp [Matrix.one_mulVec] <;> rfl)`. Take `⟨hJ, hred⟩` from `mem_congruence_of_action hc ST SG hx hy 1 (h.trans (hact _).symm)`. Use `show x⁻¹ * y ∈ (redG hc n ST SG).ker.map (J0 hc n ST).subtype`.

Conclude with `Subgroup.mem_map.2 ⟨⟨_, hJ⟩, hred, rfl⟩`.
-/
theorem mem_principal_of_same_decoration {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) (hy : y ∈ UAd hc n)
    (h : decoRaw ST SG x = decoRaw ST SG y) : x⁻¹ * y ∈ K1 hc n ST SG := by
  have hact : ∀ d : Deco E n ST SG, d.act 1 1 = d := by
    rintro ⟨N, f, be⟩
    unfold Deco.act
    congr 1
    all_goals first
      | exact Deco.act_one_N ST SG ⟨N, f, be⟩ 1
      | rfl
      | (funext w z; simp [Matrix.one_mulVec] <;> rfl)
  obtain ⟨hJ, hred⟩ := mem_congruence_of_action hc ST SG hx hy 1 (h.trans (hact _).symm)
  show x⁻¹ * y ∈ (redG hc n ST SG).ker.map (J0 hc n ST).subtype
  exact Subgroup.mem_map.2 ⟨⟨_, hJ⟩, hred, rfl⟩

/- English proof (translation)
Introduce `q₁ q₂ h`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective q₁`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective q₂`. Rewrite `h` using `[decoPt_mk, decoPt_mk]`. Establish `hx` using `hOk _ x.2`.

Establish `hy` using `hOk _ y.2`. Unfold `decoOf at h`. Rewrite `h` using `[dif_pos hx, dif_pos hy]`. Establish `hr : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `by injection h`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises.

Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]`. Conclude with `mem_principal_of_same_decoration hc n ST SG x.2 y.2 hr`.
-/
theorem decoPt_injective (hOk : DecoOfOk hc n ST SG) : Function.Injective (decoPt hc n ST SG) := by
  intro q₁ q₂ h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₂
  rw [decoPt_mk, decoPt_mk] at h
  have hx := hOk _ x.2
  have hy := hOk _ y.2
  unfold decoOf at h
  rw [dif_pos hx, dif_pos hy] at h
  have hr : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    injection h
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_principal_of_same_decoration hc n ST SG x.2 y.2 hr

variable (H : Subgroup (GLG E n SG))

/- English proof (translation)
Introduce `h`. Take `⟨q, hq⟩` from `hS (((1 : UF E n), h) • DecoSet.base E n ST SG)`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective q`. Rewrite `hq` using `[decoPt_mk]`. Establish `hy` using `hOk _ y.2`.

Unfold `decoOf at hq`. Rewrite `hq` using `[dif_pos hy]`. Establish `h1 : decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = (decoRaw ST SG (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).act 1 (h : GLG E n SG)`. Establish `h2` using `congrArg Subtype.val hq`. Rewrite using `[decoRaw_one]`.

Conclude with `h2`. Take `⟨hJ, hred⟩` from `mem_congruence_of_action hc ST SG y.2 (one_mem _) (h : GLG E n SG) h1`. Use `⟨⟨⟨_, hJ⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show redG hc n ST SG ⟨_, hJ⟩ ∈ H`. Rewrite using `[hred]`.

Conclude with `h.2`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hred`.
-/
theorem redHSurj_of (hOk : DecoOfOk hc n ST SG) (hS : Function.Surjective (decoPt hc n ST SG)) :
    RedHSurj hc n ST SG H := by
  intro h
  obtain ⟨q, hq⟩ := hS (((1 : UF E n), h) • DecoSet.base E n ST SG)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [decoPt_mk] at hq
  have hy := hOk _ y.2
  unfold decoOf at hq
  rw [dif_pos hy] at hq
  have h1 : decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      (decoRaw ST SG (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).act 1 (h : GLG E n SG) := by
    have h2 := congrArg Subtype.val hq
    rw [decoRaw_one]
    exact h2
  obtain ⟨hJ, hred⟩ := mem_congruence_of_action hc ST SG y.2 (one_mem _) (h : GLG E n SG) h1
  refine ⟨⟨⟨_, hJ⟩, ?_⟩, ?_⟩
  · show redG hc n ST SG ⟨_, hJ⟩ ∈ H
    rw [hred]
    exact h.2
  · apply Subtype.ext
    exact hred

def DecoPtSurj : Prop := Function.Surjective (decoPt hc n ST SG)

def adelicIso_of {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (o : OnDeco n ST SG H S)
    (hOk : DecoOfOk hc n ST SG) (hS : DecoPtSurj hc n ST SG) : GSD.Iso (adGSD hc o) S :=
  adelicIso hc n ST SG H o ⟨decoPt_injective hc n ST SG hOk, hS⟩ (decoPtEqv_of hc n ST SG H hOk)
    (redHSurj_of hc n ST SG H hOk hS)

end Inj2

section Ok

open Formalism.UG in

/- English proof (translation)
Establish `hfin : Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hL.lat.fg`. Establish `hspan` using `hL.lat.span_eq_top`. Establish `hint : ∀ x ∈ L, ∀ z ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) J x z)`. Introduce `x hx z hz`. Establish `hz' : z ∈ Formalism.BasicNotions.dualSet (hc.sig : E →+* E) J L` using `by rw [hL.selfdual]; exact hz`.

Take `⟨a, ha⟩` from `hz' x hx`. Rewrite using `[Int.cast_one, one_mul, ← ha]`. Conclude with `RingOfIntegers.isIntegral_coe a`. Use `⟨hL.herm, hL.unit, hL.tdef, Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) L hfin hspan y, ?_⟩` and prove the remaining obligations. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce `hz show ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (z i)) ∈ latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) L`. Use `Formalism.L2.DIV.hat_selfdual hc.sig J L hspan hL.selfdual _ fun l hl => ?_` and prove the remaining obligations. Establish `hg' : cT (sigR hc.sig (Formalism.L2.Herm.Af F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * J.map (inclE (F` using `F) (Formalism.L2.Herm.Af F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = J.map (inclE (F := F) (Formalism.L2.Herm.Af F)) := hyU`. Establish `h3` using `Formalism.UG.P.hform_mulVec (sigR hc.sig (Formalism.L2.Herm.Af F)) (J.map (inclE (F := F) (Formalism.L2.Herm.Af F))) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm …`.

Rewrite `h3` using `[hg', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[← h3]`. Use `Formalism.UG.P.csDual_span hc.sig J (Formalism.UG.CS.globLat y L) z hz _ ?_` and prove the remaining obligations. Use `Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds L hfin hspan y _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Conclude with `Submodule.subset_span ⟨l, hl, rfl⟩`. Introduce `hz x hx`. Establish `h1` using `Formalism.UG.P.csScale_glob hc.sig J L 1 hint y hyU hx hz`. Establish `h2` using `Formalism.UG.P.csGlob_int (F := F) _ h1`. Rewrite `h2` using `[Int.cast_one, one_mul]`.

Conclude with `⟨⟨_, h2⟩, rfl⟩`.
-/
theorem globLat_defUnimod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Formalism.L2.DIV.IsDefUnimod hc J L) {y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hyU : y ∈ Formalism.L2.DIV.UA hc J) :
    Formalism.L2.DIV.IsDefUnimod hc J (Formalism.UG.CS.globLat y L) := by
  have hfin : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.lat.fg
  have hspan := hL.lat.span_eq_top
  have hint : ∀ x ∈ L, ∀ z ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) J x z) := by
    intro x hx z hz
    have hz' : z ∈ Formalism.BasicNotions.dualSet (hc.sig : E →+* E) J L := by rw [hL.selfdual]; exact hz
    obtain ⟨a, ha⟩ := hz' x hx
    rw [Int.cast_one, one_mul, ← ha]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨hL.herm, hL.unit, hL.tdef, Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) L hfin hspan y, ?_⟩
  ext z
  constructor
  · intro hz
    show ((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (z i)) ∈ latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) L
    refine Formalism.L2.DIV.hat_selfdual hc.sig J L hspan hL.selfdual _ fun l hl => ?_
    have hg' : cT (sigR hc.sig (Formalism.L2.Herm.Af F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        J.map (inclE (F := F) (Formalism.L2.Herm.Af F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        J.map (inclE (F := F) (Formalism.L2.Herm.Af F)) := hyU
    have h3 := Formalism.UG.P.hform_mulVec (sigR hc.sig (Formalism.L2.Herm.Af F)) (J.map (inclE (F := F) (Formalism.L2.Herm.Af F)))
      (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (l i))
      (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (fun i => inclE (F := F) (Formalism.L2.Herm.Af F) (z i)))
    rw [hg', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h3
    rw [← h3]
    refine Formalism.UG.P.csDual_span hc.sig J (Formalism.UG.CS.globLat y L) z hz _ ?_
    refine Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds L hfin hspan y _ ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  · intro hz x hx
    have h1 := Formalism.UG.P.csScale_glob hc.sig J L 1 hint y hyU hx hz
    have h2 := Formalism.UG.P.csGlob_int (F := F) _ h1
    rw [Int.cast_one, one_mul] at h2
    exact ⟨⟨_, h2⟩, rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)

/- English proof (translation)
Establish `h : Formalism.L2.DIV.IsDefUnimod hc (Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn false : E))) (Formalism.UG.stdLat (n` using `Fin n) (A := E) (𝓞 E)) := by`. Establish `h0` using `Formalism.L2.DIV.standard_definite_unimodular F E hc n false`. Rewrite `h0` using `[Formalism.L2.DIV.stdSpace_gram]`. Conclude with `h0`. Establish `e : Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn false : E)) = 1`.

Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Rewrite `h` using `[e, ← stdLat_eq_ug]`. Conclude with `h`.
-/
theorem std_defUnimod : Formalism.L2.DIV.IsDefUnimod hc (1 : Matrix (Fin n) (Fin n) E) (stdLat E n) := by
  have h : Formalism.L2.DIV.IsDefUnimod hc (Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn false : E)))
      (Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    have h0 := Formalism.L2.DIV.standard_definite_unimodular F E hc n false
    rw [Formalism.L2.DIV.stdSpace_gram] at h0
    exact h0
  have e : Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn false : E)) = 1 := by
    rw [← Matrix.diagonal_one]; congr 1
  rw [e, ← stdLat_eq_ug] at h
  exact h

/- English proof (translation)
Use `show ∑ i, ∑ j, (hc.sig : E →+* E) (y i) * (1 : Matrix (Fin n) (Fin n) E) i j * z j = ∑ i, star (y i) * z i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne' hj, mul_zero, zero_mul]) (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]`. Both sides reduce to the same expression.
-/
theorem hform_one (y z : Fin n → E) :
    Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) y z = hStd E n y z := by
  show ∑ i, ∑ j, (hc.sig : E →+* E) (y i) * (1 : Matrix (Fin n) (Fin n) E) i j * z j = ∑ i, star (y i) * z i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne' hj, mul_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, mul_one]
  rfl

/- English proof (translation)
Establish `hd` using `globLat_defUnimod (std_defUnimod hc n) hx`. Establish `e` using `Set.ext_iff.1 hd.selfdual`. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual`. Use extensionality with `z`. Use `Iff.trans ?_ ((e z).trans SetLike.mem_coe)` and prove the remaining obligations.

Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars, Submodule.mem_one, Formalism.BasicNotions.dualSet, Set.mem_setOf_eq, hform_one, RingHom.mem_range]`.
-/
theorem globLat_unimodular {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hd := globLat_defUnimod (std_defUnimod hc n) hx
  have e := Set.ext_iff.1 hd.selfdual
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual
  ext z
  refine Iff.trans ?_ ((e z).trans SetLike.mem_coe)
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    LinearMap.coe_restrictScalars, Submodule.mem_one, Formalism.BasicNotions.dualSet, Set.mem_setOf_eq, hform_one,
    RingHom.mem_range]

end Ok

section Ok2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Establish `hm : iA F E (algebraMap (𝓞 E) E s) * (a + b) ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[mul_add]`. Conclude with `add_mem ha hb`. Apply `redA_eq P hs hm` to reduce the goal to its premises. Rewrite using `[mul_add (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs ha, redA_spec P hs hb, ← map_add]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_add]`.
-/
theorem redA_add (P : Pl E) {a b : E ⊗[F] Formalism.L2.Herm.Af F} {s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (ha : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E)
    (hb : iA F E (algebraMap (𝓞 E) E s) * b ∈ Formalism.L2.Herm.intAf F E) :
    redA P (a + b) = redA P a + redA P b := by
  have hm : iA F E (algebraMap (𝓞 E) E s) * (a + b) ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_add]
    exact add_mem ha hb
  apply redA_eq P hs hm
  rw [mul_add (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs ha, redA_spec P hs hb, ← map_add]
  congr 1
  apply Subtype.ext
  simp [mul_add]

/- English proof (translation)
Establish `hm : iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E c) * a) ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (iA_mem c) ha`. Apply `redA_eq P hs hm` to reduce the goal to its premises. Rewrite using `[mul_left_comm (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs ha, ← Formalism.L2.DIV.resS_oToS (F := F) P c, ← map_mul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, Subtype.coe_mk, ← iA_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem redA_smul (P : Pl E) {a : E ⊗[F] Formalism.L2.Herm.Af F} {s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (ha : iA F E (algebraMap (𝓞 E) E s) * a ∈ Formalism.L2.Herm.intAf F E) (c : 𝓞 E) :
    redA P (iA F E (algebraMap (𝓞 E) E c) * a) = Ideal.Quotient.mk P.asIdeal c * redA P a := by
  have hm : iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E c) * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_left_comm]
    exact mul_mem (iA_mem c) ha
  apply redA_eq P hs hm
  rw [mul_left_comm (Ideal.Quotient.mk P.asIdeal s), redA_spec P hs ha,
    ← Formalism.L2.DIV.resS_oToS (F := F) P c, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, Subtype.coe_mk, ← iA_coe]
  ring

variable {n : ℕ}

/- English proof (translation)
Take `⟨s, hs, hsv⟩` from `pullV_den hv`. Take `⟨t, ht, htw⟩` from `pullV_den hw`. Use `⟨s * t, fun h => (P.isPrime.mem_or_mem h).elim hs ht, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]`. Conclude with `mul_mem (iA_mem t) (hsv j)`.

Rewrite using `[map_mul, map_mul, mul_assoc]`. Conclude with `mul_mem (iA_mem s) (htw j)`.
-/
theorem pull_vectors_common_denominator {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {P : Pl E} {v w : Fin n → E}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)))
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ (∀ j, iA F E (algebraMap (𝓞 E) E s) * pullV x v j ∈ Formalism.L2.Herm.intAf F E) ∧
      ∀ j, iA F E (algebraMap (𝓞 E) E s) * pullV x w j ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, hs, hsv⟩ := pullV_den hv
  obtain ⟨t, ht, htw⟩ := pullV_den hw
  refine ⟨s * t, fun h => (P.isPrime.mem_or_mem h).elim hs ht, fun j => ?_, fun j => ?_⟩
  · rw [map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
    exact mul_mem (iA_mem t) (hsv j)
  · rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem s) (htw j)

/- English proof (translation)
Unfold `pullV`. Establish `h : (fun j => iA F E ((v + w) j)) = (fun j => iA F E (v j)) + fun j => iA F E (w j)`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[h, Matrix.mulVec_add]`.

Both sides reduce to the same expression.
-/
theorem pullV_add (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v w : Fin n → E) (i : Fin n) :
    pullV x (v + w) i = pullV x v i + pullV x w i := by
  unfold pullV
  have h : (fun j => iA F E ((v + w) j)) = (fun j => iA F E (v j)) + fun j => iA F E (w j) := by
    funext j
    simp
  rw [h, Matrix.mulVec_add]
  rfl

def RedKer (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) : Prop :=
  ∀ (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat x (stdLat E n) →
    (∀ i, redA P (pullV x v i) = 0) → v ∈ P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n)

variable (hc : Formalism.BasicNotions.CMData F E) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Introduce `x hx`. Establish `hloc : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat x (stdLat E n) → v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))` using `fun P v hv => le_locP P _ hv`. Use `{ lat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n) (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x uni := globLat_unimodular hc n hx f_add := ?_, f_smul := ?_, f_off := ?_, f_ne := ?_, be …` and prove the remaining obligations. Introduce `P v hv w hw`. Simplify using `only [decoRaw, Deco.at] at hv hw ⊢`.

Rewrite using `[if_pos (Submodule.add_mem _ hv hw), if_pos hv, if_pos hw, pullV_add]`. Take `⟨s, hs, h₁, h₂⟩` from `pull_vectors_common_denominator hv hw`. Conclude with `redA_add P.1 hs (h₁ _) (h₂ _)`. Introduce `P a v hv`. Simplify using `only [decoRaw, Deco.at] at hv ⊢`.

Rewrite using `[if_pos (Submodule.smul_mem _ a hv), if_pos hv, pullV_osmul]`. Take `⟨s, hs, h₁⟩` from `pullV_den hv`. Conclude with `redA_smul P.1 hs (h₁ _) a`. Introduce `P v hv`. Simplify using `only [decoRaw, Deco.at] at hv ⊢`.

Rewrite using `[if_neg hv]`. Introduce `P`. Take `⟨v, hv, hvc⟩` from `redN_surj x P.1 (Pi.single (lastIdx n) 1)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [decoRaw]`.

Rewrite using `[if_pos (hloc P.1 v hv), hvc, Pi.single_eq_same]`. Conclude with `one_ne_zero`. Introduce `w v hv u hu`. Simplify using `only [decoRaw, Deco.at] at hv hu ⊢`. Rewrite using `[if_pos (Submodule.add_mem _ hv hu), if_pos hv, if_pos hu]`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, pullV_add]`. Take `⟨s, hs, h₁, h₂⟩` from `pull_vectors_common_denominator hv hu`. Conclude with `redA_add w.1 hs (h₁ _) (h₂ _)`. Introduce `w a v hv`.

Simplify using `only [decoRaw, Deco.at] at hv ⊢`. Rewrite using `[if_pos (Submodule.smul_mem _ a hv), if_pos hv]`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul, pullV_osmul]`. Take `⟨s, hs, h₁⟩` from `pullV_den hv`.

Conclude with `redA_smul w.1 hs (h₁ _) a`. Introduce `w v hv`. Simplify using `only [decoRaw, Deco.at] at hv ⊢`. Rewrite using `[if_neg hv]`. Introduce `w c`.

Take `⟨v, hv, hvc⟩` from `redN_surj x w.1 c`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [decoRaw]`. Rewrite using `[if_pos (hloc w.1 v hv)]`. Use function extensionality and compare the values at `i`.

Conclude with `hvc i`. Introduce `w v hv h0`. Use `hK x w.1 v hv fun i => ?_` and prove the remaining obligations. Simplify using `only [decoRaw] at h0`. Rewrite `h0` using `[if_pos (hloc w.1 v hv)]`.

Conclude with `congrFun h0 i`.
-/
theorem decoOfOk_of (hK : RedKer F E n) : DecoOfOk hc n ST SG := by
  classical
  intro x hx
  have hloc : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.UG.CS.globLat x (stdLat E n) →
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) := fun P v hv => le_locP P _ hv
  refine
    { lat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
        (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
      uni := globLat_unimodular hc n hx
      f_add := ?_, f_smul := ?_, f_off := ?_, f_ne := ?_, be_add := ?_, be_smul := ?_, be_off := ?_, be_surj := ?_,
      be_ker := ?_ }
  · intro P v hv w hw
    simp only [decoRaw, Deco.at] at hv hw ⊢
    rw [if_pos (Submodule.add_mem _ hv hw), if_pos hv, if_pos hw, pullV_add]
    obtain ⟨s, hs, h₁, h₂⟩ := pull_vectors_common_denominator hv hw
    exact redA_add P.1 hs (h₁ _) (h₂ _)
  · intro P a v hv
    simp only [decoRaw, Deco.at] at hv ⊢
    rw [if_pos (Submodule.smul_mem _ a hv), if_pos hv, pullV_osmul]
    obtain ⟨s, hs, h₁⟩ := pullV_den hv
    exact redA_smul P.1 hs (h₁ _) a
  · intro P v hv
    simp only [decoRaw, Deco.at] at hv ⊢
    rw [if_neg hv]
  · intro P
    obtain ⟨v, hv, hvc⟩ := redN_surj x P.1 (Pi.single (lastIdx n) 1)
    refine ⟨v, hv, ?_⟩
    simp only [decoRaw]
    rw [if_pos (hloc P.1 v hv), hvc, Pi.single_eq_same]
    exact one_ne_zero
  · intro w v hv u hu
    simp only [decoRaw, Deco.at] at hv hu ⊢
    rw [if_pos (Submodule.add_mem _ hv hu), if_pos hv, if_pos hu]
    funext i
    rw [Pi.add_apply, pullV_add]
    obtain ⟨s, hs, h₁, h₂⟩ := pull_vectors_common_denominator hv hu
    exact redA_add w.1 hs (h₁ _) (h₂ _)
  · intro w a v hv
    simp only [decoRaw, Deco.at] at hv ⊢
    rw [if_pos (Submodule.smul_mem _ a hv), if_pos hv]
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pullV_osmul]
    obtain ⟨s, hs, h₁⟩ := pullV_den hv
    exact redA_smul w.1 hs (h₁ _) a
  · intro w v hv
    simp only [decoRaw, Deco.at] at hv ⊢
    rw [if_neg hv]
  · intro w c
    obtain ⟨v, hv, hvc⟩ := redN_surj x w.1 c
    refine ⟨v, hv, ?_⟩
    simp only [decoRaw]
    rw [if_pos (hloc w.1 v hv)]
    funext i; exact hvc i
  · intro w v hv h0
    refine hK x w.1 v hv fun i => ?_
    simp only [decoRaw] at h0
    rw [if_pos (hloc w.1 v hv)] at h0
    exact congrFun h0 i

end Ok2

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `hs1 : (1 : 𝓞 E) ∉ P.asIdeal` using `fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hm : iA F E (algebraMap (𝓞 E) E 1) * a ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[map_one, map_one, one_mul]`. Conclude with `ha`. Apply `redA_eq P hs1 hm` to reduce the goal to its premises.

Rewrite using `[map_one, one_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subtype.coe_mk, map_one, one_mul]`.
-/
theorem redA_int (P : Pl E) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) :
    redA P a = resS F P ⟨a, ha⟩ := by
  have hs1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hm : iA F E (algebraMap (𝓞 E) E 1) * a ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_one, map_one, one_mul]
    exact ha
  apply redA_eq P hs1 hm
  rw [map_one, one_mul]
  congr 1
  apply Subtype.ext
  simp only [Subtype.coe_mk, map_one, one_mul]

/- English proof (translation)
Establish `h' : (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal) (Formalism.L2.DIV.cmpS_bij (F` using `F) P.asIdeal P.ne_bot)).symm (Ideal.Quotient.mk (Formalism.L2.DIV.idS F P.asIdeal) t) = 0 := h`. Rewrite `h'` using `[map_eq_zero_iff _ (RingEquiv.injective _)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h'`.
-/
theorem mem_idS_of_resS {P : Pl E} {t : Formalism.L2.Herm.intAf F E} (h : resS F P t = 0) : t ∈ Formalism.L2.DIV.idS F P.asIdeal := by
  have h' : (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm
      (Ideal.Quotient.mk (Formalism.L2.DIV.idS F P.asIdeal) t) = 0 := h
  rw [map_eq_zero_iff _ (RingEquiv.injective _)] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h'

/- English proof (translation)
Establish `key : ∀ p ∈ P.asIdeal, ∀ w ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N, Formalism.L2.DIV.oToS F E p • w ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • N) := by`. Introduce `p hp w hw`. Establish `hw' : w ∈ Submodule.span (Formalism.L2.Herm.intAf F E) ((fun x : Fin n → E => fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (x i)) '' (N : Set (Fin n → E))) := hw`. Use `clear hw`. Proceed by induction on `hw' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨p • y, Submodule.smul_mem_smul hp hy, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • y) i) = ((Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Consider the case `zero`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ ihx ihy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ihx ihy`. Consider the case `smul a x _ ihx`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ a ihx`. Establish `ht' : t ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (Formalism.L2.DIV.oToS F E '' (P.asIdeal : Set (𝓞 E)))` using `ht`. Use `clear ht`. Proceed by induction on `ht' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨p, hp, rfl⟩` from `hx`. Conclude with `key p hp u hu`. Consider the case `zero`. Rewrite using `[zero_smul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ ihx ihy`. Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ ihx ihy`. Consider the case `smul a x _ ihx`.

Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ a ihx`.
-/
theorem idS_smul_span (P : Pl E) (N : Submodule (𝓞 E) (Fin n → E)) {t : Formalism.L2.Herm.intAf F E}
    (ht : t ∈ Formalism.L2.DIV.idS F P.asIdeal) {u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hu : u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N) :
    t • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • N) := by
  have key : ∀ p ∈ P.asIdeal, ∀ w ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N,
      Formalism.L2.DIV.oToS F E p • w ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • N) := by
    intro p hp w hw
    have hw' : w ∈ Submodule.span (Formalism.L2.Herm.intAf F E) ((fun x : Fin n → E => fun i =>
        Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (N : Set (Fin n → E))) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨p • y, Submodule.smul_mem_smul hp hy, ?_⟩
      funext i
      show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • y) i) =
        ((Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) *
          Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
      rw [smul_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x _ ihx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a ihx
  have ht' : t ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (Formalism.L2.DIV.oToS F E '' (P.asIdeal : Set (𝓞 E))) := ht
  clear ht
  induction ht' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact key p hp u hu
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [add_smul]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
    rw [smul_eq_mul, mul_smul]
    exact Submodule.smul_mem _ a ihx

open scoped Pointwise in
/- English proof (translation)
Use `haveI : IsNoetherian (𝓞 E) N := isNoetherian_of_fg_of_noetherian N hN.fg`. Use `haveI : IsNoetherian (𝓞 E) ↥(P.asIdeal • N) := isNoetherian_of_le Submodule.smul_le_right`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hN.span_eq_top, Submodule.span_le]`. Introduce `x hx`.

Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Establish `hpE : algebraMap (𝓞 E) E p ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hp0`. Establish `h1 : p • x ∈ Submodule.span E ((P.asIdeal • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))` using `Submodule.subset_span (Submodule.smul_mem_smul hp hx)`. Establish `e : x = (algebraMap (𝓞 E) E p)⁻¹ • (p • x)`. Rewrite using `[← algebraMap_smul E p x, inv_smul_smul₀ hpE]`.

Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem smul_lattice (P : Pl E) {N : Submodule (𝓞 E) (Fin n → E)} (hN : Submodule.IsLattice E N) :
    Module.Finite (𝓞 E) ↥(P.asIdeal • N : Submodule (𝓞 E) (Fin n → E)) ∧ Submodule.span E ((P.asIdeal • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  haveI : IsNoetherian (𝓞 E) N := isNoetherian_of_fg_of_noetherian N hN.fg
  haveI : IsNoetherian (𝓞 E) ↥(P.asIdeal • N) := isNoetherian_of_le Submodule.smul_le_right
  refine ⟨inferInstance, ?_⟩
  rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
  intro x hx
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hpE : algebraMap (𝓞 E) E p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hp0
  have h1 : p • x ∈ Submodule.span E ((P.asIdeal • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul hp hx)
  have e : x = (algebraMap (𝓞 E) E p)⁻¹ • (p • x) := by
    rw [← algebraMap_smul E p x, inv_smul_smul₀ hpE]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ h1

/- English proof (translation)
Introduce `x P v hv h0`. Establish `hfin` using `Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg`. Establish `hspan` using `(stdLat_lattice (E := E) (n := n)).span_eq_top`. Establish `hNl` using `Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n) hfin hspan x`. Establish `hSR` using `Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan x`.

Establish `hz : ∀ i, pullV x v i ∈ Formalism.L2.Herm.intAf F E` using `(mem_globLat x v).1 hv`. Establish `hidS : ∀ i, (⟨_, hz i⟩ : Formalism.L2.Herm.intAf F E) ∈ Formalism.L2.DIV.idS F P.asIdeal`. Introduce `i`. Apply `mem_idS_of_resS` to reduce the goal to its premises. Rewrite using `[← redA_int]`.

Conclude with `h0 i`. Establish `hcol : ∀ i, (x : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.UG.CS.globLat x (stdLat E n)) := by`. Introduce `i`. Use `(hSR _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, mem_latS_std]`.

Introduce `j`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `Subring.one_mem _`.

Rewrite using `[Pi.single_eq_of_ne hij]`. Conclude with `Subring.zero_mem _`. Establish `hιv : (fun i => iA F E (v i)) = ∑ i, (⟨_, hz i⟩ : Formalism.L2.Herm.intAf F E) • ((x : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F))`. Establish `e1 : (fun i => iA F E (v i)) = (x : Matrix (Fin n) (Fin n) _) *ᵥ pullV x v`. Unfold `pullV`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[e1]`. Establish `e2 : pullV x v = ∑ i, pullV x v i • (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `conv_lhs => rw [e2]`. Rewrite using `[Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression.

Establish `hmem : (fun i => iA F E (v i)) ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n)) := by`. Rewrite using `[hιv]`. Conclude with `Submodule.sum_mem _ fun i _ => idS_smul_span P _ (hidS i) (hcol i)`. Establish `hPN` using `smul_lattice P hNl`. Establish `hone` using `Formalism.UG.P.global_lattice_one_holds F E (Fin n) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n)) hPN.1 hPN.2`.

Rewrite using `[← hone]`. Use `show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (fun i => iA F E (v i)) ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n))`. Rewrite using `[inv_one, Units.val_one, Matrix.one_mulVec]`. Conclude with `hmem`.
-/
theorem reduction_kernel_equality : RedKer F E n := by
  classical
  intro x P v hv h0
  have hfin := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg
  have hspan := (stdLat_lattice (E := E) (n := n)).span_eq_top
  have hNl := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n) hfin hspan x
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan x
  have hz : ∀ i, pullV x v i ∈ Formalism.L2.Herm.intAf F E := (mem_globLat x v).1 hv
  have hidS : ∀ i, (⟨_, hz i⟩ : Formalism.L2.Herm.intAf F E) ∈ Formalism.L2.DIV.idS F P.asIdeal := by
    intro i
    apply mem_idS_of_resS
    rw [← redA_int]; exact h0 i

  have hcol : ∀ i, (x : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.UG.CS.globLat x (stdLat E n)) := by
    intro i
    refine (hSR _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, mem_latS_std]
    intro j
    by_cases hij : j = i
    · subst hij; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact Subring.zero_mem _
  have hιv : (fun i => iA F E (v i)) = ∑ i, (⟨_, hz i⟩ : Formalism.L2.Herm.intAf F E) •
      ((x : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : (fun i => iA F E (v i)) = (x : Matrix (Fin n) (Fin n) _) *ᵥ pullV x v := by
      unfold pullV
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e1]
    have e2 : pullV x v = ∑ i, pullV x v i • (Pi.single i 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e2]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul]
    rfl
  have hmem : (fun i => iA F E (v i)) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n)) := by
    rw [hιv]
    exact Submodule.sum_mem _ fun i _ => idS_smul_span P _ (hidS i) (hcol i)
  have hPN := smul_lattice P hNl
  have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n)) hPN.1 hPN.2
  rw [← hone]
  show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ (fun i => iA F E (v i)) ∈
    Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (P.asIdeal • Formalism.UG.CS.globLat x (stdLat E n))
  rw [inv_one, Units.val_one, Matrix.one_mulVec]
  exact hmem

end Ker

section Final

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Conclude with `decoOfOk_of hc ST SG reduction_kernel_equality`.
-/
theorem decorated_lattice_exists : DecoOfOk hc n ST SG := by
  exact decoOfOk_of hc ST SG reduction_kernel_equality

def adelicIsoS {K : Type} [Field K] [NumberField K] [StarRing K] (H : Subgroup (GLG E n SG)) {S : GSD K}
    (o : OnDeco n ST SG H S) (hS : DecoPtSurj hc n ST SG) : GSD.Iso (adGSD hc o) S :=
  adelicIso_of hc n ST SG H o (decorated_lattice_exists hc n ST SG) hS

/- English proof (translation)
Conclude with `decoPt_injective hc n ST SG (decorated_lattice_exists hc n ST SG)`.
-/
theorem decoPt_injective' : Function.Injective (decoPt hc n ST SG) := by
  exact decoPt_injective hc n ST SG (decorated_lattice_exists hc n ST SG)

/- English proof (translation)
Conclude with `decoPtEqv_of hc n ST SG H (decorated_lattice_exists hc n ST SG)`.
-/
theorem decorated_point_equivariant (H : Subgroup (GLG E n SG)) : DecoPtEqv hc n ST SG H := by
  exact decoPtEqv_of hc n ST SG H (decorated_lattice_exists hc n ST SG)

end Final

section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

def OnDeco.triv (K : Type) [Field K] [NumberField K] [StarRing K] :
    OnDeco n ST SG H (GSD.triv K (UF E n × H) (DecoSet E n ST SG)) :=
  ⟨MulEquiv.refl _, Equiv.refl _, fun _ _ => rfl⟩

end Inst

section LinAlg

variable {R κ V : Type} [CommRing R] [Field κ] [AddCommGroup V] [Module R V] {n : ℕ}

/- English proof (translation)
Use `choose u hu hu' using fun j : Fin n => hsurj (Pi.single j 1)`. Use `choose r hr using fun b => hπ b`. Set `Φ : N →+ (Fin n → κ)` to `AddMonoidHom.mk' (fun x => φ x) (fun a b => hφa a a.2 b b.2)`. Set `Ψ : N →+ (Fin n → κ)` to `AddMonoidHom.mk' (fun x => ψ x) (fun a b => hψa a a.2 b b.2)`. Use `⟨Matrix.of fun i j => ψ (u j) i, fun v hv => ?_⟩` and prove the remaining obligations.

Set `g : Fin n → N` to `fun j => ⟨r (φ v j) • u j, N.smul_mem _ (hu j)⟩`. Establish `hgφ : Φ (∑ j, g j) = φ v`. Rewrite using `[map_sum]`. Establish `e : ∀ j, Φ (g j) = φ v j • Pi.single j (1 : κ)` using `fun j => by show φ (r (φ v j) • u j) = _`. Rewrite using `[hφs _ _ (hu j), hu' j, hr]`.

Rewrite using `[Finset.sum_congr rfl fun j _ => e j]`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hgψ : Ψ (∑ j, g j) = Matrix.of (fun i j => ψ (u j) i) *ᵥ φ v`. Rewrite using `[map_sum]`.

Establish `e : ∀ j, Ψ (g j) = φ v j • ψ (u j)` using `fun j => by show ψ (r (φ v j) • u j) = _`. Rewrite using `[hψs _ _ (hu j), hr]`. Rewrite using `[Finset.sum_congr rfl fun j _ => e j]`. Use extensionality with `i`. Use `show (∑ j, φ v j • ψ (u j)) i = ∑ j, ψ (u j) i * φ v j`.

Rewrite using `[Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => by simp [mul_comm]`. Establish `hw : Φ (⟨v, hv⟩ - ∑ j, g j) = 0`. Rewrite using `[map_sub, hgφ]`. Conclude with `sub_self _`.

Establish `hψw : Ψ (⟨v, hv⟩ - ∑ j, g j) = 0` using `hker _ (⟨v, hv⟩ - ∑ j, g j : N).2 hw`. Rewrite `hψw` using `[map_sub, sub_eq_zero]`. Conclude with `hψw.trans hgψ`.
-/
theorem lin_factor (π : R →+* κ) (hπ : Function.Surjective π) (N : Submodule R V) (φ ψ : V → (Fin n → κ))
    (hφa : ∀ v ∈ N, ∀ w ∈ N, φ (v + w) = φ v + φ w) (hφs : ∀ (a : R), ∀ v ∈ N, φ (a • v) = π a • φ v)
    (hψa : ∀ v ∈ N, ∀ w ∈ N, ψ (v + w) = ψ v + ψ w) (hψs : ∀ (a : R), ∀ v ∈ N, ψ (a • v) = π a • ψ v)
    (hsurj : ∀ c, ∃ v ∈ N, φ v = c) (hker : ∀ v ∈ N, φ v = 0 → ψ v = 0) :
    ∃ M : Matrix (Fin n) (Fin n) κ, ∀ v ∈ N, ψ v = M *ᵥ φ v := by
  classical
  choose u hu hu' using fun j : Fin n => hsurj (Pi.single j 1)
  choose r hr using fun b => hπ b
  let Φ : N →+ (Fin n → κ) := AddMonoidHom.mk' (fun x => φ x) (fun a b => hφa a a.2 b b.2)
  let Ψ : N →+ (Fin n → κ) := AddMonoidHom.mk' (fun x => ψ x) (fun a b => hψa a a.2 b b.2)
  refine ⟨Matrix.of fun i j => ψ (u j) i, fun v hv => ?_⟩
  let g : Fin n → N := fun j => ⟨r (φ v j) • u j, N.smul_mem _ (hu j)⟩
  have hgφ : Φ (∑ j, g j) = φ v := by
    rw [map_sum]
    have e : ∀ j, Φ (g j) = φ v j • Pi.single j (1 : κ) := fun j => by
      show φ (r (φ v j) • u j) = _
      rw [hφs _ _ (hu j), hu' j, hr]
    rw [Finset.sum_congr rfl fun j _ => e j]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hgψ : Ψ (∑ j, g j) = Matrix.of (fun i j => ψ (u j) i) *ᵥ φ v := by
    rw [map_sum]
    have e : ∀ j, Ψ (g j) = φ v j • ψ (u j) := fun j => by
      show ψ (r (φ v j) • u j) = _
      rw [hψs _ _ (hu j), hr]
    rw [Finset.sum_congr rfl fun j _ => e j]
    ext i
    show (∑ j, φ v j • ψ (u j)) i = ∑ j, ψ (u j) i * φ v j
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  have hw : Φ (⟨v, hv⟩ - ∑ j, g j) = 0 := by
    rw [map_sub, hgφ]
    exact sub_self _
  have hψw : Ψ (⟨v, hv⟩ - ∑ j, g j) = 0 := hker _ (⟨v, hv⟩ - ∑ j, g j : N).2 hw
  rw [map_sub, sub_eq_zero] at hψw
  exact hψw.trans hgψ

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, l k ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hl (funext h)`. Set `M : Matrix (Fin n) (Fin n) κ` to `Matrix.of fun i j => if i = lastIdx n then l j else if i = k then (if j = lastIdx n then 1 else 0) else (if j = i then 1 else 0)`.

Establish `hrow : ∀ x : Fin n → κ, ∀ i, (M *ᵥ x) i = ∑ j, M i j * x j` using `fun x i => rfl`. Establish `hker : ∀ x : Fin n → κ, M *ᵥ x = 0 → x = 0`. Introduce `x hx`. Establish `h0 : ∀ i, i ≠ k → x i = 0`. Introduce `i hik`.

Distinguish the cases in `hiL : i = lastIdx n`. Establish `hkL : k ≠ lastIdx n` using `fun h => hik (hiL.trans h.symm)`. Establish `h1` using `congrFun hx k`. Rewrite `h1` using `[hrow]`. Simplify `h1` using `[M, hkL, hiL]`.

Establish `h1` using `congrFun hx i`. Rewrite `h1` using `[hrow]`. Simplify `h1` using `[M, hiL, hik]`. Establish `hxk : x k = 0`. Establish `h1` using `congrFun hx (lastIdx n)`.

Rewrite `h1` using `[hrow]`. Simplify using `only [M, Matrix.of_apply, eq_self_iff_true, if_true, Pi.zero_apply] at h1`. Rewrite `h1` using `[Finset.sum_eq_single k (fun j _ hj => by rw [h0 j hj, mul_zero]) (fun h => absurd (Finset.mem_univ k) h)]`. Conclude with `(mul_eq_zero.1 h1).resolve_left hk`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hik : i = k`. Rewrite using `[hik, hxk]`. Both sides reduce to the same expression. Conclude with `h0 i hik`. Establish `hdet : M.det ≠ 0` using `fun h => by`.

Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Conclude with `hx0 (hker x hx)`. Establish `hU : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)`. Use `⟨hU.unit, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`.

Simplify using `[M]`.
-/
theorem exists_GL_lastRow [NeZero n] (l : Fin n → κ) (hl : l ≠ 0) :
    ∃ A : GL (Fin n) κ, ∀ j, (A : Matrix (Fin n) (Fin n) κ) (lastIdx n) j = l j := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, l k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl (funext h)
  let M : Matrix (Fin n) (Fin n) κ := Matrix.of fun i j =>
    if i = lastIdx n then l j else if i = k then (if j = lastIdx n then 1 else 0) else (if j = i then 1 else 0)
  have hrow : ∀ x : Fin n → κ, ∀ i, (M *ᵥ x) i = ∑ j, M i j * x j := fun x i => rfl
  have hker : ∀ x : Fin n → κ, M *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h0 : ∀ i, i ≠ k → x i = 0 := by
      intro i hik
      by_cases hiL : i = lastIdx n
      · have hkL : k ≠ lastIdx n := fun h => hik (hiL.trans h.symm)
        have h1 := congrFun hx k
        rw [hrow] at h1
        simpa [M, hkL, hiL] using h1
      · have h1 := congrFun hx i
        rw [hrow] at h1
        simpa [M, hiL, hik] using h1
    have hxk : x k = 0 := by
      have h1 := congrFun hx (lastIdx n)
      rw [hrow] at h1
      simp only [M, Matrix.of_apply, eq_self_iff_true, if_true, Pi.zero_apply] at h1
      rw [Finset.sum_eq_single k (fun j _ hj => by rw [h0 j hj, mul_zero])
        (fun h => absurd (Finset.mem_univ k) h)] at h1
      exact (mul_eq_zero.1 h1).resolve_left hk
    funext i
    by_cases hik : i = k
    · rw [hik, hxk]
      rfl
    · exact h0 i hik
  have hdet : M.det ≠ 0 := fun h => by
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hx0 (hker x hx)
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hU.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [M]

end LinAlg

section SurjRed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Unfold `pullV`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mulVec_mulVec]`.
-/
theorem pullV_mul_inv (x k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : Fin n → E) :
    pullV (x * k⁻¹) v = (k : Matrix (Fin n) (Fin n) _) *ᵥ pullV x v := by
  unfold pullV
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite `hk` using `[St_one]`. Establish `hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, z ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ (k : Matrix (Fin n) (Fin n) _) *ᵥ z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := hk`. Establish `e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔ pullV y v ∈ Formalism.UG.latS (F` using `F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm`. Use extensionality with `v`. Rewrite using `[e, e, pullV_mul_inv]`.

Conclude with `(hk' (pullV x v)).symm`.
-/
theorem globLat_mul_St (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    Formalism.UG.CS.globLat (x * k⁻¹) (stdLat E n) = Formalism.UG.CS.globLat x (stdLat E n) := by
  rw [St_one] at hk
  have hk' : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      z ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔
        (k : Matrix (Fin n) (Fin n) _) *ᵥ z ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) := hk
  have e : ∀ y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), ∀ v : Fin n → E, v ∈ Formalism.UG.CS.globLat y (stdLat E n) ↔
      pullV y v ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) :=
    fun y v => (mem_globLat y v).trans (mem_latS_std (pullV y v)).symm
  ext v
  rw [e, e, pullV_mul_inv]
  exact (hk' (pullV x v)).symm

/- English proof (translation)
Establish `key : v ∈ N ∧ ψ v = 0`. Use `Submodule.smul_induction_on hv ?_ ?_` and prove the remaining obligations. Introduce `r hr w hw`. Use `⟨N.smul_mem r hw, ?_⟩` and prove the remaining obligations. Rewrite using `[hs r w hw, (Ideal.Quotient.eq_zero_iff_mem).2 hr, zero_smul]`.

Introduce and unpack `x y ⟨hx, hx0⟩ ⟨hy, hy0⟩`. Conclude with `⟨N.add_mem hx hy, by rw [ha x hx y hy, hx0, hy0, add_zero]⟩`. Conclude with `key.2`.
-/
theorem kill_smul {P : Pl E} {N : Submodule (𝓞 E) (Fin n → E)} {m : ℕ} (ψ : (Fin n → E) → (Fin m → kP P))
    (ha : ∀ v ∈ N, ∀ w ∈ N, ψ (v + w) = ψ v + ψ w)
    (hs : ∀ (a : 𝓞 E), ∀ v ∈ N, ψ (a • v) = Ideal.Quotient.mk P.asIdeal a • ψ v) {v : Fin n → E}
    (hv : v ∈ P.asIdeal • N) : ψ v = 0 := by
  have key : v ∈ N ∧ ψ v = 0 := by
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro r hr w hw
      refine ⟨N.smul_mem r hw, ?_⟩
      rw [hs r w hw, (Ideal.Quotient.eq_zero_iff_mem).2 hr, zero_smul]
    · rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
      exact ⟨N.add_mem hx hy, by rw [ha x hx y hy, hx0, hy0, add_zero]⟩
  exact key.2

end SurjRed

section SurjThm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

open Classical in

/- English proof (translation)
Introduce and unpack `⟨d, ok⟩`. Take `⟨x0, hx0, hN⟩` from `hG d.N ok.lat ok.uni`. Use `set N0 := Formalism.UG.CS.globLat x0 (stdLat E n) with hN0`. Set `r : ∀ P : Pl E, (Fin n → E) → Fin n → kP P` to `fun P v i => redA P (pullV x0 v i)`. Establish `hint : ∀ v ∈ N0, ∀ j, iA F E (algebraMap (𝓞 E) E 1) * pullV x0 v j ∈ Formalism.L2.Herm.intAf F E`.

Introduce `v hv j`. Rewrite using `[map_one, map_one, one_mul]`. Conclude with `(mem_globLat x0 v).1 hv j`. Establish `hra : ∀ P : Pl E, ∀ v ∈ N0, ∀ w ∈ N0, r P (v + w) = r P v + r P w`. Introduce `P v hv w hw`.

Use function extensionality and compare the values at `i`. Use `show redA P (pullV x0 (v + w) i) = redA P (pullV x0 v i) + redA P (pullV x0 w i)`. Rewrite using `[pullV_add]`. Conclude with `redA_add P (one_notMem P) (hint v hv i) (hint w hw i)`. Establish `hrs : ∀ P : Pl E, ∀ (a : 𝓞 E), ∀ v ∈ N0, r P (a • v) = Ideal.Quotient.mk P.asIdeal a • r P v`.

Introduce `P a v hv`. Use function extensionality and compare the values at `i`. Use `show redA P (pullV x0 (a • v) i) = Ideal.Quotient.mk P.asIdeal a * redA P (pullV x0 v i)`. Rewrite using `[pullV_osmul]`. Conclude with `redA_smul P (one_notMem P) (hint v hv i) a`.

Establish `hrsurj : ∀ (P : Pl E) (c : Fin n → kP P), ∃ v ∈ N0, r P v = c`. Introduce `P c`. Take `⟨v, hv, hvc⟩` from `redN_surj x0 P c`. Conclude with `⟨v, hv, funext hvc⟩`. Establish `hrker : ∀ (P : Pl E), ∀ v ∈ N0, r P v = 0 → v ∈ P.asIdeal • N0` using `fun P v hv h0 => reduction_kernel_equality x0 P v hv fun i => congrFun h0 i`.

Establish `hmem : ∀ v, v ∈ N0 ↔ v ∈ d.N` using `fun v => by rw [hN]`. Establish `hexY : ∀ w : SG, ∃ Y : GL (Fin n) (kP w.1), ∀ v ∈ N0, d.be w v = (Y : Matrix (Fin n) (Fin n) _) *ᵥ r w.1 v`. Introduce `w`. Establish `hba : ∀ v ∈ N0, ∀ u ∈ N0, d.be w (v + u) = d.be w v + d.be w u` using `fun v hv u hu => ok.be_add w v (le_locP w.1 _ ((hmem v).1 hv)) u (le_locP w.1 _ ((hmem u).1 hu))`. Establish `hbs : ∀ (a : 𝓞 E), ∀ v ∈ N0, d.be w (a • v) = Ideal.Quotient.mk w.1.asIdeal a • d.be w v` using `fun a v hv => ok.be_smul w a v (le_locP w.1 _ ((hmem v).1 hv))`.

Take `⟨M, hM⟩` from `lin_factor (Ideal.Quotient.mk w.1.asIdeal) Ideal.Quotient.mk_surjective N0 (r w.1) (d.be w) (hra w.1) (hrs w.1) hba hbs (hrsurj w.1) (fun v hv h0 => kill_smul n (d.be w) hba hbs (hrker w.1 v hv h0))`. Take `⟨M', hM'⟩` from `lin_factor (Ideal.Quotient.mk w.1.asIdeal) Ideal.Quotient.mk_surjective N0 (d.be w) (r w.1) hba hbs (hra w.1) (hrs w.1) (fun c => by`. Take `⟨v, hv, hvc⟩` from `ok.be_surj w c`. Conclude with `⟨v, (hmem v).2 hv, hvc⟩)`. Use the proof step `(fun v hv h0 => by`.

Establish `h1` using `ok.be_ker w v ((hmem v).1 hv) h0`. Rewrite `h1` using `[← hN]`. Conclude with `kill_smul n (r w.1) (hra w.1) (hrs w.1) h1)`. Establish `hMM : M * M' = 1`. Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations.

Take `⟨v, hv, hvc⟩` from `ok.be_surj w (Pi.single j 1)`. Rewrite using `[Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← hvc, ← hM' v ((hmem v).2 hv), ← hM v ((hmem v).2 hv)]`. Conclude with `⟨⟨M, M', hMM, mul_eq_one_comm.1 hMM⟩, hM⟩`. Use `choose Y hY using hexY`. Establish `hexA : ∀ P : ST, ∃ A : GL (Fin n) (kP P.1), ∀ v ∈ N0, d.f P v = ∑ j, (A : Matrix (Fin n) (Fin n) _) (lastIdx n) j * r P.1 v j`.

Introduce `P`. Set `ψ : (Fin n → E) → Fin n → kP P.1` to `fun v _ => d.f P v`. Establish `hfa : ∀ v ∈ N0, ∀ u ∈ N0, ψ (v + u) = ψ v + ψ u` using `fun v hv u hu => funext fun _ => ok.f_add P v (le_locP P.1 _ ((hmem v).1 hv)) u (le_locP P.1 _ ((hmem u).1 hu))`. Establish `hfs : ∀ (a : 𝓞 E), ∀ v ∈ N0, ψ (a • v) = Ideal.Quotient.mk P.1.asIdeal a • ψ v` using `fun a v hv => funext fun _ => ok.f_smul P a v (le_locP P.1 _ ((hmem v).1 hv))`. Take `⟨M, hM⟩` from `lin_factor (Ideal.Quotient.mk P.1.asIdeal) Ideal.Quotient.mk_surjective N0 (r P.1) ψ (hra P.1) (hrs P.1) hfa hfs (hrsurj P.1) (fun v hv h0 => kill_smul n ψ hfa hfs (hrker P.1 v hv h0))`.

Establish `hl : (fun j => M (lastIdx n) j) ≠ 0`. Introduce `h0`. Take `⟨v, hv, hfv⟩` from `ok.f_ne P`. Apply `hfv` to reduce the goal to its premises. Establish `h1` using `congrFun (hM v ((hmem v).2 hv)) (lastIdx n)`.

Use `show ψ v (lastIdx n) = 0`. Rewrite using `[h1, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [show M (lastIdx n) j = 0 from congrFun h0 j, zero_mul]`. Take `⟨A, hA⟩` from `exists_GL_lastRow _ hl`. Use `⟨A, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrFun (hM v hv) (lastIdx n)`. Rewrite using `[show d.f P v = ψ v (lastIdx n) from rfl, h1, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hA j]`. Use `choose A hA using hexA`. Set `y : ∀ P : ↥(ST ∪ SG), GL (Fin n) (kP P.1)` to `fun P => if h : P.1 ∈ ST then A ⟨P.1, h⟩ else Y ⟨P.1, (Finset.mem_union.1 P.2).resolve_left h⟩`.

Establish `hdef : Formalism.L2.DIV.IsDefUnimod hc (1 : Matrix (Fin n) (Fin n) E) (Formalism.UG.stdLat (n` using `Fin n) (A := E) (𝓞 E)) := by`. Establish `h` using `std_defUnimod hc n`. Rewrite `h` using `[stdLat_eq_ug]`. Conclude with `h`. Take `⟨k, hk, hky⟩` from `hR F E hc n 1 _ 1 (ST ∪ SG) hdef (Formalism.L2.DIV.frame_standard F E n) hT y`.

Establish `hkS : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `hk.2`. Take `⟨z, hzk, hzr⟩` from `St_one_int hkS`. Establish `hred : ∀ (P : ↥(ST ∪ SG)) (i j : Fin n), ((y P : GL (Fin n) (kP P.1)) : Matrix (Fin n) (Fin n) _) i j = resS F P.1 (z i j)`. Introduce `P i j`. Establish `h` using `hky P`.

Rewrite `h` using `[Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hkS]`. Rewrite using `[← h, hzr P.1 i j]`. Use `set x := x0 * k⁻¹ with hxdef`. Establish `hxU : x ∈ UAd hc n` using `Subgroup.mul_mem _ hx0 (Subgroup.inv_mem _ hk.1)`. Establish `hNx : Formalism.UG.CS.globLat x (stdLat E n) = N0` using `globLat_mul_St n x0 hkS`.

Establish `hvalN : ∀ (P : Pl E), ∀ u ∈ N0, ∀ i, redA P (pullV x u i) = ∑ j, resS F P (z i j) * r P u j`. Introduce `P u hu i`. Rewrite using `[hxdef, pullV_mul_inv, mulVec_int_apply hzk]`. Conclude with `redA_sum P (one_notMem P) _ (hint u hu) _`. Establish `hscale : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N0 → ∀ (s : 𝓞 E) (i : Fin n), redA P (pullV x (s • v) i) = Ideal.Quotient.mk P.asIdeal s * redA P (pullV x v i)`.

Introduce `P v hv s i`. Rewrite `hv` using `[← hNx]`. Take `⟨s', hs', hden⟩` from `pullV_den hv`. Rewrite using `[pullV_osmul]`. Conclude with `redA_smul P hs' (hden i) s`.

Use `⟨((⟨x, hxU⟩ : UAd hc n) : adPt hc n ST SG), ?_⟩` and prove the remaining obligations. Rewrite using `[decoPt_mk]`. Unfold `decoOf`. Rewrite using `[dif_pos (decorated_lattice_exists hc n ST SG x hxU)]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show decoRaw ST SG x = d`. Use `ext1`. Use `show Formalism.UG.CS.globLat x (stdLat E n) = d.N`. Rewrite using `[hNx, hN]`. Use function extensionality and compare the values at `P v show (if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then redA P.1 (pullV x v (lastIdx n)) else 0) = d.f P v`.

Distinguish the cases in `hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))`. Rewrite using `[if_pos hv]`. Establish `hv0 : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N0` using `by rwa [hNx] at hv`. Establish `hv' : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N` using `by rwa [← hN]`. Take `⟨s, hs, hsv⟩` from `(mem_locP P.1 _ v).1 hv'`.

Establish `hsv0 : s • v ∈ N0` using `(hmem _).2 hsv`. Apply `mul_left_cancel₀ (mk_ne_zero hs)` to reduce the goal to its premises. Rewrite using `[← hscale P.1 v hv0 s, hvalN P.1 _ hsv0, ← ok.f_smul P s v hv', hA P _ hsv0]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hPu : P.1 ∈ ST ∪ SG` using `Finset.mem_union_left _ P.2`.

Establish `h1` using `hred ⟨P.1, hPu⟩ (lastIdx n) j`. Establish `h2 : y ⟨P.1, hPu⟩ = A P` using `by simp only [y, dif_pos P.2]`. Rewrite `h1` using `[h2]`. Rewrite using `[h1]`. Rewrite using `[if_neg hv]`.

Establish `hv' : v ∉ Deco.at d P.1` using `by show v ∉ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N`. Rewrite `hv` using `[hNx, hN]`. Then use the resulting hypothesis. Conclude with `(ok.f_off P v hv').symm`. Use function extensionality and compare the values at `w v show (if v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then fun i => redA w.1 (pullV x v i) else 0) = d.be w v`. Distinguish the cases in `hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))`.

Rewrite using `[if_pos hv]`. Establish `hv0 : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal N0` using `by rwa [hNx] at hv`. Establish `hv' : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal d.N` using `by rwa [← hN]`. Take `⟨s, hs, hsv⟩` from `(mem_locP w.1 _ v).1 hv'`. Establish `hsv0 : s • v ∈ N0` using `(hmem _).2 hsv`.

Use function extensionality and compare the values at `i`. Apply `mul_left_cancel₀ (mk_ne_zero hs)` to reduce the goal to its premises. Establish `hbs` using `congrFun (ok.be_smul w s v hv') i`. Rewrite `hbs` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← hscale w.1 v hv0 s, hvalN w.1 _ hsv0, ← hbs, hY w _ hsv0, Matrix.mulVec, dotProduct]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hwu : w.1 ∈ ST ∪ SG` using `Finset.mem_union_right _ w.2`. Establish `hwS : w.1 ∉ ST` using `fun h => Finset.disjoint_left.1 hD h w.2`. Establish `h1` using `hred ⟨w.1, hwu⟩ i j`. Establish `h2 : y ⟨w.1, hwu⟩ = Y w` using `by simp only [y, dif_neg hwS]`.

Rewrite `h1` using `[h2]`. Rewrite using `[h1]`. Rewrite using `[if_neg hv]`. Establish `hv' : v ∉ Deco.at d w.1` using `by show v ∉ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal d.N`. Rewrite `hv` using `[hNx, hN]`. Then use the resulting hypothesis.

Conclude with `(ok.be_off w v hv').symm`.
-/
theorem decoPtSurj_of (hG : UnimodGenus hc n) (hR : Formalism.L2.DIV.RedSurj) (hT : Formalism.L2.DIV.IsSplitSet (ST ∪ SG))
    (hD : Disjoint ST SG) : DecoPtSurj hc n ST SG := by
  classical
  rintro ⟨d, ok⟩
  obtain ⟨x0, hx0, hN⟩ := hG d.N ok.lat ok.uni
  set N0 := Formalism.UG.CS.globLat x0 (stdLat E n) with hN0
  let r : ∀ P : Pl E, (Fin n → E) → Fin n → kP P := fun P v i => redA P (pullV x0 v i)
  have hint : ∀ v ∈ N0, ∀ j, iA F E (algebraMap (𝓞 E) E 1) * pullV x0 v j ∈ Formalism.L2.Herm.intAf F E := by
    intro v hv j; rw [map_one, map_one, one_mul]; exact (mem_globLat x0 v).1 hv j
  have hra : ∀ P : Pl E, ∀ v ∈ N0, ∀ w ∈ N0, r P (v + w) = r P v + r P w := by
    intro P v hv w hw; funext i
    show redA P (pullV x0 (v + w) i) = redA P (pullV x0 v i) + redA P (pullV x0 w i)
    rw [pullV_add]; exact redA_add P (one_notMem P) (hint v hv i) (hint w hw i)
  have hrs : ∀ P : Pl E, ∀ (a : 𝓞 E), ∀ v ∈ N0, r P (a • v) = Ideal.Quotient.mk P.asIdeal a • r P v := by
    intro P a v hv; funext i
    show redA P (pullV x0 (a • v) i) = Ideal.Quotient.mk P.asIdeal a * redA P (pullV x0 v i)
    rw [pullV_osmul]; exact redA_smul P (one_notMem P) (hint v hv i) a
  have hrsurj : ∀ (P : Pl E) (c : Fin n → kP P), ∃ v ∈ N0, r P v = c := by
    intro P c
    obtain ⟨v, hv, hvc⟩ := redN_surj x0 P c
    exact ⟨v, hv, funext hvc⟩
  have hrker : ∀ (P : Pl E), ∀ v ∈ N0, r P v = 0 → v ∈ P.asIdeal • N0 :=
    fun P v hv h0 => reduction_kernel_equality x0 P v hv fun i => congrFun h0 i
  have hmem : ∀ v, v ∈ N0 ↔ v ∈ d.N := fun v => by rw [hN]

  have hexY : ∀ w : SG, ∃ Y : GL (Fin n) (kP w.1), ∀ v ∈ N0, d.be w v = (Y : Matrix (Fin n) (Fin n) _) *ᵥ r w.1 v := by
    intro w
    have hba : ∀ v ∈ N0, ∀ u ∈ N0, d.be w (v + u) = d.be w v + d.be w u := fun v hv u hu =>
      ok.be_add w v (le_locP w.1 _ ((hmem v).1 hv)) u (le_locP w.1 _ ((hmem u).1 hu))
    have hbs : ∀ (a : 𝓞 E), ∀ v ∈ N0, d.be w (a • v) = Ideal.Quotient.mk w.1.asIdeal a • d.be w v := fun a v hv =>
      ok.be_smul w a v (le_locP w.1 _ ((hmem v).1 hv))
    obtain ⟨M, hM⟩ := lin_factor (Ideal.Quotient.mk w.1.asIdeal) Ideal.Quotient.mk_surjective N0 (r w.1) (d.be w)
      (hra w.1) (hrs w.1) hba hbs (hrsurj w.1) (fun v hv h0 => kill_smul n (d.be w) hba hbs (hrker w.1 v hv h0))
    obtain ⟨M', hM'⟩ := lin_factor (Ideal.Quotient.mk w.1.asIdeal) Ideal.Quotient.mk_surjective N0 (d.be w) (r w.1)
      hba hbs (hra w.1) (hrs w.1) (fun c => by
        obtain ⟨v, hv, hvc⟩ := ok.be_surj w c
        exact ⟨v, (hmem v).2 hv, hvc⟩)
      (fun v hv h0 => by
        have h1 := ok.be_ker w v ((hmem v).1 hv) h0
        rw [← hN] at h1
        exact kill_smul n (r w.1) (hra w.1) (hrs w.1) h1)
    have hMM : M * M' = 1 := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      obtain ⟨v, hv, hvc⟩ := ok.be_surj w (Pi.single j 1)
      rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← hvc, ← hM' v ((hmem v).2 hv), ← hM v ((hmem v).2 hv)]
    exact ⟨⟨M, M', hMM, mul_eq_one_comm.1 hMM⟩, hM⟩
  choose Y hY using hexY

  have hexA : ∀ P : ST, ∃ A : GL (Fin n) (kP P.1), ∀ v ∈ N0,
      d.f P v = ∑ j, (A : Matrix (Fin n) (Fin n) _) (lastIdx n) j * r P.1 v j := by
    intro P
    let ψ : (Fin n → E) → Fin n → kP P.1 := fun v _ => d.f P v
    have hfa : ∀ v ∈ N0, ∀ u ∈ N0, ψ (v + u) = ψ v + ψ u := fun v hv u hu => funext fun _ =>
      ok.f_add P v (le_locP P.1 _ ((hmem v).1 hv)) u (le_locP P.1 _ ((hmem u).1 hu))
    have hfs : ∀ (a : 𝓞 E), ∀ v ∈ N0, ψ (a • v) = Ideal.Quotient.mk P.1.asIdeal a • ψ v := fun a v hv => funext fun _ =>
      ok.f_smul P a v (le_locP P.1 _ ((hmem v).1 hv))
    obtain ⟨M, hM⟩ := lin_factor (Ideal.Quotient.mk P.1.asIdeal) Ideal.Quotient.mk_surjective N0 (r P.1) ψ
      (hra P.1) (hrs P.1) hfa hfs (hrsurj P.1) (fun v hv h0 => kill_smul n ψ hfa hfs (hrker P.1 v hv h0))
    have hl : (fun j => M (lastIdx n) j) ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hfv⟩ := ok.f_ne P
      apply hfv
      have h1 := congrFun (hM v ((hmem v).2 hv)) (lastIdx n)
      show ψ v (lastIdx n) = 0
      rw [h1, Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [show M (lastIdx n) j = 0 from congrFun h0 j, zero_mul]
    obtain ⟨A, hA⟩ := exists_GL_lastRow _ hl
    refine ⟨A, fun v hv => ?_⟩
    have h1 := congrFun (hM v hv) (lastIdx n)
    rw [show d.f P v = ψ v (lastIdx n) from rfl, h1, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hA j]
  choose A hA using hexA

  let y : ∀ P : ↥(ST ∪ SG), GL (Fin n) (kP P.1) := fun P =>
    if h : P.1 ∈ ST then A ⟨P.1, h⟩ else Y ⟨P.1, (Finset.mem_union.1 P.2).resolve_left h⟩
  have hdef : Formalism.L2.DIV.IsDefUnimod hc (1 : Matrix (Fin n) (Fin n) E) (Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    have h := std_defUnimod hc n; rw [stdLat_eq_ug] at h; exact h
  obtain ⟨k, hk, hky⟩ := hR F E hc n 1 _ 1 (ST ∪ SG) hdef (Formalism.L2.DIV.frame_standard F E n) hT y
  have hkS : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hk.2
  obtain ⟨z, hzk, hzr⟩ := St_one_int hkS
  have hred : ∀ (P : ↥(ST ∪ SG)) (i j : Fin n), ((y P : GL (Fin n) (kP P.1)) : Matrix (Fin n) (Fin n) _) i j =
      resS F P.1 (z i j) := by
    intro P i j
    have h := hky P
    rw [Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hkS] at h
    rw [← h, hzr P.1 i j]
  set x := x0 * k⁻¹ with hxdef
  have hxU : x ∈ UAd hc n := Subgroup.mul_mem _ hx0 (Subgroup.inv_mem _ hk.1)
  have hNx : Formalism.UG.CS.globLat x (stdLat E n) = N0 := globLat_mul_St n x0 hkS
  have hvalN : ∀ (P : Pl E), ∀ u ∈ N0, ∀ i, redA P (pullV x u i) = ∑ j, resS F P (z i j) * r P u j := by
    intro P u hu i
    rw [hxdef, pullV_mul_inv, mulVec_int_apply hzk]
    exact redA_sum P (one_notMem P) _ (hint u hu) _
  have hscale : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N0 → ∀ (s : 𝓞 E) (i : Fin n),
      redA P (pullV x (s • v) i) = Ideal.Quotient.mk P.asIdeal s * redA P (pullV x v i) := by
    intro P v hv s i
    rw [← hNx] at hv
    obtain ⟨s', hs', hden⟩ := pullV_den hv
    rw [pullV_osmul]
    exact redA_smul P hs' (hden i) s
  refine ⟨((⟨x, hxU⟩ : UAd hc n) : adPt hc n ST SG), ?_⟩
  rw [decoPt_mk]
  unfold decoOf
  rw [dif_pos (decorated_lattice_exists hc n ST SG x hxU)]
  apply Subtype.ext
  show decoRaw ST SG x = d
  ext1
  · show Formalism.UG.CS.globLat x (stdLat E n) = d.N
    rw [hNx, hN]
  · funext P v
    show (if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then redA P.1 (pullV x v (lastIdx n))
      else 0) = d.f P v
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
    · rw [if_pos hv]
      have hv0 : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N0 := by rwa [hNx] at hv
      have hv' : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by rwa [← hN]
      obtain ⟨s, hs, hsv⟩ := (mem_locP P.1 _ v).1 hv'
      have hsv0 : s • v ∈ N0 := (hmem _).2 hsv
      apply mul_left_cancel₀ (mk_ne_zero hs)
      rw [← hscale P.1 v hv0 s, hvalN P.1 _ hsv0, ← ok.f_smul P s v hv', hA P _ hsv0]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hPu : P.1 ∈ ST ∪ SG := Finset.mem_union_left _ P.2
      have h1 := hred ⟨P.1, hPu⟩ (lastIdx n) j
      have h2 : y ⟨P.1, hPu⟩ = A P := by simp only [y, dif_pos P.2]
      rw [h2] at h1
      rw [h1]
    · rw [if_neg hv]
      have hv' : v ∉ Deco.at d P.1 := by
        show v ∉ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N
        rwa [hNx, hN] at hv
      exact (ok.f_off P v hv').symm
  · funext w v
    show (if v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then fun i => redA w.1 (pullV x v i)
      else 0) = d.be w v
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
    · rw [if_pos hv]
      have hv0 : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal N0 := by rwa [hNx] at hv
      have hv' : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal d.N := by rwa [← hN]
      obtain ⟨s, hs, hsv⟩ := (mem_locP w.1 _ v).1 hv'
      have hsv0 : s • v ∈ N0 := (hmem _).2 hsv
      funext i
      apply mul_left_cancel₀ (mk_ne_zero hs)
      have hbs := congrFun (ok.be_smul w s v hv') i
      rw [Pi.smul_apply, smul_eq_mul] at hbs
      rw [← hscale w.1 v hv0 s, hvalN w.1 _ hsv0, ← hbs, hY w _ hsv0, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hwu : w.1 ∈ ST ∪ SG := Finset.mem_union_right _ w.2
      have hwS : w.1 ∉ ST := fun h => Finset.disjoint_left.1 hD h w.2
      have h1 := hred ⟨w.1, hwu⟩ i j
      have h2 : y ⟨w.1, hwu⟩ = Y w := by simp only [y, dif_neg hwS]
      rw [h2] at h1
      rw [h1]
    · rw [if_neg hv]
      have hv' : v ∉ Deco.at d w.1 := by
        show v ∉ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal d.N
        rwa [hNx, hN] at hv
      exact (ok.be_off w v hv').symm

open Classical in

def adelicIsoG {K : Type} [Field K] [NumberField K] [StarRing K] (H : Subgroup (GLG E n SG)) {S : GSD K}
    (o : OnDeco n ST SG H S) (hG : UnimodGenus hc n) (hR : Formalism.L2.DIV.RedSurj) (hT : Formalism.L2.DIV.IsSplitSet (ST ∪ SG))
    (hD : Disjoint ST SG) : GSD.Iso (adGSD hc o) S :=
  adelicIsoS hc n ST SG H o (decoPtSurj_of hc n ST SG hG hR hT hD)

end SurjThm

end Formalism.L2.Col
