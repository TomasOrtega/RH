import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.EichCont

section Abstract

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}

def IntV (v : Fin N → E) : Prop := ∀ j, v j ∈ O

def Bd (A : Module.End E (Fin N → E)) (t : F) : Prop :=
  ∀ m, IntV O m → ∃ m', IntV O m' ∧ A m = algebraMap F E t • m'

def Cont {Q : Type} (near : F → Q → Prop) (G : Q → Module.End E (Fin N → E))
    (A : Module.End E (Fin N → E)) : Prop :=
  ∀ c : F, c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → Bd O (G q - A) c

variable {O}

/- English proof (translation)
Introduce `j` and use `O.add_mem (hv j) (hw j)`.
-/
theorem IntV.add {v w : Fin N → E} (hv : IntV O v) (hw : IntV O w) : IntV O (v + w) :=
  fun j => O.add_mem (hv j) (hw j)

/- English proof (translation)
Introduce `j` and use `O.mul_mem hz (hv j)`.
-/
theorem IntV.smul {z : E} (hz : z ∈ O) {v : Fin N → E} (hv : IntV O v) : IntV O (z • v) :=
  fun j => O.mul_mem hz (hv j)

/- English proof (translation)
Introduce `_` and use `O.zero_mem`.
-/
theorem IntV.zero : IntV O (0 : Fin N → E) := fun _ => O.zero_mem

/- English proof (translation)
Introduce `m hm`. Take `⟨m', hm', e⟩` from `h m hm`. Conclude with `⟨algebraMap F E o • m', hm'.smul ho, by rw [e, map_mul, mul_smul]⟩`.
-/
theorem Bd.mono {A : Module.End E (Fin N → E)} {t o : F} (h : Bd O A (t * o))
    (ho : algebraMap F E o ∈ O) : Bd O A t := by
  intro m hm
  obtain ⟨m', hm', e⟩ := h m hm
  exact ⟨algebraMap F E o • m', hm'.smul ho, by rw [e, map_mul, mul_smul]⟩

/- English proof (translation)
Introduce `m hm`. Take `⟨a, ha, ea⟩` from `hA m hm`. Take `⟨b, hb, eb⟩` from `hB m hm`. Conclude with `⟨a + b, ha.add hb, by rw [LinearMap.add_apply, ea, eb, smul_add]⟩`.
-/
theorem Bd.add {A B : Module.End E (Fin N → E)} {t : F} (hA : Bd O A t) (hB : Bd O B t) :
    Bd O (A + B) t := by
  intro m hm
  obtain ⟨a, ha, ea⟩ := hA m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  exact ⟨a + b, ha.add hb, by rw [LinearMap.add_apply, ea, eb, smul_add]⟩

/- English proof (translation)
Introduce `m hm`. Take `⟨b, hb, eb⟩` from `hB m hm`. Take `⟨a, ha, ea⟩` from `hA b hb`. Conclude with `⟨a, ha, by rw [Module.End.mul_apply, eb, map_smul, ea, smul_smul, ← map_mul, mul_comm]⟩`.
-/
theorem Bd.mul {A B : Module.End E (Fin N → E)} {t s : F} (hA : Bd O A t) (hB : Bd O B s) :
    Bd O (A * B) (t * s) := by
  intro m hm
  obtain ⟨b, hb, eb⟩ := hB m hm
  obtain ⟨a, ha, ea⟩ := hA b hb
  exact ⟨a, ha, by rw [Module.End.mul_apply, eb, map_smul, ea, smul_smul, ← map_mul, mul_comm]⟩

/- English proof (translation)
Introduce `_ _` and use `⟨0, IntV.zero, by simp⟩`.
-/
theorem Bd.zero (t : F) : Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, IntV.zero, by simp⟩

variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

/- English proof (translation)
Use `choose a ha0 haO haz using fun i => hden (z i)`. Establish `hP : ∀ s : Finset ι, algebraMap F E (∏ i ∈ s, a i) ∈ O` using `fun s => by`. Rewrite using `[map_prod]`. Conclude with `prod_mem fun i _ => haO i`. Use `⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i, hP _, fun i => ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap F E (∏ j, a j) * z i = algebraMap F E (∏ j ∈ Finset.univ.erase i, a j) * (algebraMap F E (a i) * z i)`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `O.mul_mem (hP _) (haz i)`.
-/
theorem exists_den {ι : Type} [Fintype ι] (z : ι → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ i, algebraMap F E a * z i ∈ O := by
  choose a ha0 haO haz using fun i => hden (z i)
  have hP : ∀ s : Finset ι, algebraMap F E (∏ i ∈ s, a i) ∈ O := fun s => by
    rw [map_prod]; exact prod_mem fun i _ => haO i
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i, hP _, fun i => ?_⟩
  have e : algebraMap F E (∏ j, a j) * z i =
      algebraMap F E (∏ j ∈ Finset.univ.erase i, a j) * (algebraMap F E (a i) * z i) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul]; ring
  rw [e]
  exact O.mul_mem (hP _) (haz i)

/- English proof (translation)
Take `⟨w, hw0, hwO, hw⟩` from `exists_den hden (fun p : Fin N × Fin N => A (fun j => if p.1 = j then 1 else 0) p.2)`. Use `⟨w, hw0, hwO, fun m hm => ⟨∑ i, m i • (algebraMap F E w • A (fun j => if i = j then 1 else 0)), fun j => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Conclude with `sum_mem fun i _ => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Conclude with `O.mul_mem (hm i) (hw (i, j))`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ A m, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm (m i) (algebraMap F E w), smul_smul, ← map_mul, inv_mul_cancel₀ hw0, map_one, one_smul]`.
-/
theorem Bd.exists (A : Module.End E (Fin N → E)) :
    ∃ w : F, w ≠ 0 ∧ algebraMap F E w ∈ O ∧ Bd O A w⁻¹ := by
  obtain ⟨w, hw0, hwO, hw⟩ := exists_den hden
    (fun p : Fin N × Fin N => A (fun j => if p.1 = j then 1 else 0) p.2)
  refine ⟨w, hw0, hwO, fun m hm =>
    ⟨∑ i, m i • (algebraMap F E w • A (fun j => if i = j then 1 else 0)), fun j => ?_, ?_⟩⟩
  · rw [Finset.sum_apply]
    exact sum_mem fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact O.mul_mem (hm i) (hw (i, j))
  · rw [LinearMap.pi_apply_eq_sum_univ A m, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm (m i) (algebraMap F E w), smul_smul, ← map_mul, inv_mul_cancel₀ hw0, map_one,
      one_smul]

/- English proof (translation)
Introduce `c hc`. Take `⟨w₁, hw₁, hw₁O, hA⟩` from `Bd.exists hden A`. Take `⟨w₂, hw₂, hw₂O, hB⟩` from `Bd.exists hden B`. Take `⟨ε, hε, hεO, hεc⟩` from `hden (algebraMap F E c⁻¹)`. Establish `hεc' : algebraMap F E (ε * c⁻¹) ∈ O` using `by rw [map_mul]; exact hεc`.

Establish `hwO : algebraMap F E (w₁ * w₂) ∈ O` using `by rw [map_mul]; exact O.mul_mem hw₁O hw₂O`. Establish `hA' : Bd O A (w₁ * w₂)⁻¹` using `Bd.mono (o := w₂) (by rwa [show (w₁ * w₂)⁻¹ * w₂ = w₁⁻¹ by field_simp]) hw₂O`. Establish `hB' : Bd O B (w₁ * w₂)⁻¹` using `Bd.mono (o := w₁) (by rwa [show (w₁ * w₂)⁻¹ * w₁ = w₂⁻¹ by field_simp]) hw₁O`. Establish `hα : ε * (w₁ * w₂) ≠ 0` using `mul_ne_zero hε (mul_ne_zero hw₁ hw₂)`. Take `⟨d₁, hd₁, h1⟩` from `hG _ hα`.

Take `⟨d₂, hd₂, h2⟩` from `hH _ hα`. Take `⟨d, hd, hn⟩` from `hnear d₁ d₂ hd₁ hd₂`. Use `⟨d, hd, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hGq` using `h1 q (hn q hq).1`. Establish `hHq` using `h2 q (hn q hq).2`.

Establish `e : G q * H q - A * B = (G q - A) * (H q - B) + ((G q - A) * B + A * (H q - B))` using `by noncomm_ring`. Use `show Bd O (G q * H q - A * B) c`. Rewrite using `[e]`. Use `Bd.add ?_ (Bd.add ?_ ?_)` and prove the remaining obligations. Use `Bd.mono (o := (ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) ?_ ?_` and prove the remaining obligations.

Rewrite using `[show c * ((ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) = (ε * (w₁ * w₂)) * (ε * (w₁ * w₂)) by field_simp]`. Conclude with `hGq.mul hHq`. Establish `hwO' : algebraMap F E w₁ * algebraMap F E w₂ ∈ O` using `O.mul_mem hw₁O hw₂O`. Simplify using `only [map_mul]`. Conclude with `O.mul_mem hεc (O.mul_mem (O.mul_mem hεO hwO') hwO')`.

Use `Bd.mono (o := ε * c⁻¹) ?_ hεc'` and prove the remaining obligations. Rewrite using `[show c * (ε * c⁻¹) = (ε * (w₁ * w₂)) * (w₁ * w₂)⁻¹ by field_simp]`. Conclude with `hGq.mul hB'`. Use `Bd.mono (o := ε * c⁻¹) ?_ hεc'` and prove the remaining obligations. Rewrite using `[show c * (ε * c⁻¹) = (w₁ * w₂)⁻¹ * (ε * (w₁ * w₂)) by field_simp]`.

Conclude with `hA'.mul hHq`.
-/
theorem Cont.mul {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q)
    {G H : Q → Module.End E (Fin N → E)} {A B : Module.End E (Fin N → E)}
    (hG : Cont O near G A) (hH : Cont O near H B) : Cont O near (fun q => G q * H q) (A * B) := by
  intro c hc
  obtain ⟨w₁, hw₁, hw₁O, hA⟩ := Bd.exists hden A
  obtain ⟨w₂, hw₂, hw₂O, hB⟩ := Bd.exists hden B
  obtain ⟨ε, hε, hεO, hεc⟩ := hden (algebraMap F E c⁻¹)
  have hεc' : algebraMap F E (ε * c⁻¹) ∈ O := by rw [map_mul]; exact hεc
  have hwO : algebraMap F E (w₁ * w₂) ∈ O := by rw [map_mul]; exact O.mul_mem hw₁O hw₂O
  have hA' : Bd O A (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₂) (by rwa [show (w₁ * w₂)⁻¹ * w₂ = w₁⁻¹ by field_simp]) hw₂O
  have hB' : Bd O B (w₁ * w₂)⁻¹ :=
    Bd.mono (o := w₁) (by rwa [show (w₁ * w₂)⁻¹ * w₁ = w₂⁻¹ by field_simp]) hw₁O
  have hα : ε * (w₁ * w₂) ≠ 0 := mul_ne_zero hε (mul_ne_zero hw₁ hw₂)
  obtain ⟨d₁, hd₁, h1⟩ := hG _ hα
  obtain ⟨d₂, hd₂, h2⟩ := hH _ hα
  obtain ⟨d, hd, hn⟩ := hnear d₁ d₂ hd₁ hd₂
  refine ⟨d, hd, fun q hq => ?_⟩
  have hGq := h1 q (hn q hq).1
  have hHq := h2 q (hn q hq).2
  have e : G q * H q - A * B = (G q - A) * (H q - B) + ((G q - A) * B + A * (H q - B)) := by
    noncomm_ring
  show Bd O (G q * H q - A * B) c
  rw [e]
  refine Bd.add ?_ (Bd.add ?_ ?_)
  · refine Bd.mono (o := (ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) ?_ ?_
    · rw [show c * ((ε * c⁻¹) * (ε * (w₁ * w₂) * (w₁ * w₂))) = (ε * (w₁ * w₂)) * (ε * (w₁ * w₂)) by
        field_simp]
      exact hGq.mul hHq
    · have hwO' : algebraMap F E w₁ * algebraMap F E w₂ ∈ O := O.mul_mem hw₁O hw₂O
      simp only [map_mul]
      exact O.mul_mem hεc (O.mul_mem (O.mul_mem hεO hwO') hwO')
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (ε * (w₁ * w₂)) * (w₁ * w₂)⁻¹ by field_simp]
    exact hGq.mul hB'
  · refine Bd.mono (o := ε * c⁻¹) ?_ hεc'
    rw [show c * (ε * c⁻¹) = (w₁ * w₂)⁻¹ * (ε * (w₁ * w₂)) by field_simp]
    exact hA'.mul hHq

/- English proof (translation)
The claim follows from `| 0, G, A, _ => fun c _ => ⟨1, one_ne_zero, fun q _ => by simpa using Bd.zero (O := O) (N := N) c⟩ | r + 1, G, A, h => by simp only [List.ofFn_succ, List.prod_cons] exact Cont.mul hden hnear (h 0) (Cont.prod hnear r (fun i => G i.succ) (fun i => A i.succ) fun i => h i.succ)`.
-/
theorem Cont.prod {Q : Type} {near : F → Q → Prop}
    (hnear : ∀ a b : F, a ≠ 0 → b ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ q, near d q → near a q ∧ near b q) :
    ∀ (r : ℕ) (G : Fin r → Q → Module.End E (Fin N → E)) (A : Fin r → Module.End E (Fin N → E)),
      (∀ i, Cont O near (G i) (A i)) →
      Cont O near (fun q => (List.ofFn fun i => G i q).prod) (List.ofFn A).prod
  | 0, G, A, _ => fun c _ => ⟨1, one_ne_zero, fun q _ => by simpa using Bd.zero (O := O) (N := N) c⟩
  | r + 1, G, A, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact Cont.mul hden hnear (h 0)
      (Cont.prod hnear r (fun i => G i.succ) (fun i => A i.succ) fun i => h i.succ)

end Abstract

section Eich

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

end Eich

section Lat

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {O : Subring E} {N : ℕ}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

end Lat

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
/- English proof (translation)
Establish `hint : ∀ t : F, ∃ s : F, s ≠ 0 ∧ s ∈ (valuation F).integer ∧ s * t ∈ (valuation F).integer`. Introduce `t`. Distinguish the cases in `ht : valuation F t ≤ 1`. Conclude with `⟨1, one_ne_zero, (valuation F).integer.one_mem, by`. Rewrite using `[one_mul, Valuation.mem_integer_iff]`.

Conclude with `ht⟩`. Establish `ht0 : t ≠ 0` using `by rintro rfl; exact ht (by simp)`. Use `⟨t⁻¹, inv_ne_zero ht0, ?_, by` and prove the remaining obligations. Rewrite using `[inv_mul_cancel₀ ht0]`. Conclude with `(valuation F).integer.one_mem⟩`.

Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ (le_of_lt (not_le.1 ht))`. Take `⟨ω, hωO, e, -, hωe⟩` from `_root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L`. Take `⟨x, y, hxy⟩` from `_root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := F) (L.cj : E →+* E) (fun x => L.cj_cj x) (fun r => L.cj.commutes r) (fun x hx => by obtain ⟨a, ha⟩ := (L.cj_fix x).1 hx; exact ⟨a, ha⟩) ⟨⟨_, e, hωe, by rw [mul_comm]; exact hωe⟩, rfl⟩ z`. Take `⟨s₁, hs₁0, hs₁, hs₁x⟩` from `hint x`.

Take `⟨s₂, hs₂0, hs₂, hs₂y⟩` from `hint y`. Establish `hO : ∀ t ∈ (valuation F).integer, algebraMap F E t ∈ L.O` using `fun t ht => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L t).2 ht`. Use `⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, hO _ ((valuation F).integer.mul_mem hs₁ hs₂), ?_⟩` and prove the remaining obligations. Rewrite using `[hxy]`. Establish `: algebraMap F E (s₁ * s₂) * (algebraMap F E x + algebraMap F E y * ω) = algebraMap F E s₂ * algebraMap F E (s₁ * x) + algebraMap F E s₁ * algebraMap F E (s₂ * y) * ω`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.O.add_mem (L.O.mul_mem (hO _ hs₂) (hO _ hs₁x)) (L.O.mul_mem (L.O.mul_mem (hO _ hs₁) (hO _ hs₂y)) hωO)`.
-/
private lemma exists_algebraMap_mul_mem_O {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (z : E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧ algebraMap F E a * z ∈ L.O := by
  have hint : ∀ t : F, ∃ s : F, s ≠ 0 ∧ s ∈ (valuation F).integer ∧
      s * t ∈ (valuation F).integer := by
    intro t
    by_cases ht : valuation F t ≤ 1
    · exact ⟨1, one_ne_zero, (valuation F).integer.one_mem, by
        rw [one_mul, Valuation.mem_integer_iff]; exact ht⟩
    · have ht0 : t ≠ 0 := by rintro rfl; exact ht (by simp)
      refine ⟨t⁻¹, inv_ne_zero ht0, ?_, by
        rw [inv_mul_cancel₀ ht0]; exact (valuation F).integer.one_mem⟩
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 ht))
  obtain ⟨ω, hωO, e, -, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  obtain ⟨x, y, hxy⟩ := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := F) (L.cj : E →+* E)
    (fun x => L.cj_cj x) (fun r => L.cj.commutes r)
    (fun x hx => by obtain ⟨a, ha⟩ := (L.cj_fix x).1 hx; exact ⟨a, ha⟩)
    ⟨⟨_, e, hωe, by rw [mul_comm]; exact hωe⟩, rfl⟩ z
  obtain ⟨s₁, hs₁0, hs₁, hs₁x⟩ := hint x
  obtain ⟨s₂, hs₂0, hs₂, hs₂y⟩ := hint y
  have hO : ∀ t ∈ (valuation F).integer, algebraMap F E t ∈ L.O :=
    fun t ht => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L t).2 ht
  refine ⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, hO _ ((valuation F).integer.mul_mem hs₁ hs₂), ?_⟩
  rw [hxy]
  have : algebraMap F E (s₁ * s₂) * (algebraMap F E x + algebraMap F E y * ω) =
      algebraMap F E s₂ * algebraMap F E (s₁ * x) +
        algebraMap F E s₁ * algebraMap F E (s₂ * y) * ω := by
    simp only [map_mul]; ring
  rw [this]
  exact L.O.add_mem (L.O.mul_mem (hO _ hs₂) (hO _ hs₁x))
    (L.O.mul_mem (L.O.mul_mem (hO _ hs₁) (hO _ hs₂y)) hωO)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
/- English proof (translation)
Use `choose a ha0 haO haz using fun k => hden (z k)`. Use `⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha0 k, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `O.prod_mem fun k _ => haO k`. Rewrite using `[map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc]`.

Conclude with `O.mul_mem (O.prod_mem fun k' _ => haO k') (haz k)`.
-/
private lemma exists_algebraMap_mul_mem_O_forall {κ : Type} [Fintype κ] (z : κ → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ k, algebraMap F E a * z k ∈ O := by
  choose a ha0 haO haz using fun k => hden (z k)
  refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha0 k, ?_, fun k => ?_⟩
  · rw [map_prod]
    exact O.prod_mem fun k _ => haO k
  · rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k' _ => haO k') (haz k)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
/- English proof (translation)
Take `⟨a, ha0, haO, haz⟩` from `exists_algebraMap_mul_mem_O_forall hden (fun p : Fin N × Fin N => A (fun k => if p.1 = k then 1 else 0) p.2)`. Use `⟨a, ha0, haO, fun m hm => ⟨algebraMap F E a • A m, fun i => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ A m]`. Simplify using `only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `O.sum_mem fun j _ => by`.

Rewrite using `[mul_left_comm]`. Conclude with `O.mul_mem (hm j) (haz (j, i))`. Rewrite using `[smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]`.
-/
private lemma exists_algebraMap_mem_O_Bd_inv (A : Module.End E (Fin N → E)) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ _root_.GlobalTheory.HL.EichCont.Bd O A a⁻¹ := by
  obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : Fin N × Fin N => A (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨a, ha0, haO, fun m hm => ⟨algebraMap F E a • A m, fun i => ?_, ?_⟩⟩
  · rw [LinearMap.pi_apply_eq_sum_univ A m]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact O.sum_mem fun j _ => by
      rw [mul_left_comm]
      exact O.mul_mem (hm j) (haz (j, i))
  · rw [smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `_ _` and use `⟨0, fun _ => O.zero_mem, by simp⟩`.
-/
private lemma Bd_zero' (t : F) : _root_.GlobalTheory.HL.EichCont.Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, fun _ => O.zero_mem, by simp⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `j` and use `by simpa using O.mul_mem ho (hm j)`.
-/
private lemma IntV_smul_of_mem {o : E} (ho : o ∈ O) {m : Fin N → E}
    (hm : _root_.GlobalTheory.HL.EichCont.IntV O m) : _root_.GlobalTheory.HL.EichCont.IntV O (o • m) :=
  fun j => by simpa using O.mul_mem ho (hm j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `m hm`. Take `⟨m₁, hm₁, e₁⟩` from `hA m hm`. Conclude with `⟨algebraMap F E o • m₁, IntV_smul_of_mem ho hm₁, by rw [e₁, map_mul, mul_smul]⟩`.
-/
private lemma Bd_of_Bd_mul_of_mem_O {A : Module.End E (Fin N → E)} {s o : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A (s * o)) (ho : algebraMap F E o ∈ O) :
    _root_.GlobalTheory.HL.EichCont.Bd O A s := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  exact ⟨algebraMap F E o • m₁, IntV_smul_of_mem ho hm₁, by rw [e₁, map_mul, mul_smul]⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
The claim follows from `h ▸ hA`.
-/
private lemma Bd_of_eq {A : Module.End E (Fin N → E)} {s t : F} (h : s = t)
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) : _root_.GlobalTheory.HL.EichCont.Bd O A t := h ▸ hA

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `j` and use `O.add_mem (hm j) (hm' j)`.
-/
private lemma IntV_add' {m m' : Fin N → E} (hm : _root_.GlobalTheory.HL.EichCont.IntV O m)
    (hm' : _root_.GlobalTheory.HL.EichCont.IntV O m') : _root_.GlobalTheory.HL.EichCont.IntV O (m + m') :=
  fun j => O.add_mem (hm j) (hm' j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `m hm`. Take `⟨m₁, hm₁, e₁⟩` from `hA m hm`. Take `⟨m₂, hm₂, e₂⟩` from `hB m hm`. Conclude with `⟨m₁ + m₂, IntV_add' hm₁ hm₂, by rw [LinearMap.add_apply, e₁, e₂, smul_add]⟩`.
-/
private lemma Bd_add' {A B : Module.End E (Fin N → E)} {t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A t) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A + B) t := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hB m hm
  exact ⟨m₁ + m₂, IntV_add' hm₁ hm₂, by rw [LinearMap.add_apply, e₁, e₂, smul_add]⟩

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
/- English proof (translation)
Introduce `m hm`. Take `⟨m₁, hm₁, e₁⟩` from `hB m hm`. Take `⟨m₂, hm₂, e₂⟩` from `hA m₁ hm₁`. Use `⟨m₂, hm₂, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, e₁, map_smul, e₂, smul_smul, ← map_mul, mul_comm t s]`.
-/
private lemma Bd_mul' {A B : Module.End E (Fin N → E)} {s t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A * B) (s * t) := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hB m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hA m₁ hm₁
  refine ⟨m₂, hm₂, ?_⟩
  rw [Module.End.mul_apply, e₁, map_smul, e₂, smul_smul, ← map_mul, mul_comm t s]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `A c _`. Conclude with `⟨1, one_ne_zero, fun G _ => by`.

Simplify using `only [List.ofFn_zero, List.prod_nil, sub_self]`. Conclude with `Bd_zero' c⟩`. Consider the case `succ r ih`. Introduce `A c hc`. Take `⟨a, ha0, haO, hA0⟩` from `exists_algebraMap_mem_O_Bd_inv hden (A 0)`.

Take `⟨b, hb0, hbO, hAs⟩` from `exists_algebraMap_mem_O_Bd_inv hden (List.ofFn fun i => A i.succ).prod`. Take `⟨w, hw0, hwO, hwc⟩` from `hden (algebraMap F E c)`. Take `⟨d₁, hd₁0, hd₁⟩` from `ih (fun i => A i.succ) (c * a * b * w) (by simp [hc, ha0, hb0, hw0])`. Take `⟨z, hz0, hzO, hz⟩` from `exists_algebraMap_mul_mem_O_forall hden ![algebraMap F E (c * b), algebraMap F E d₁]`. Establish `hz1 : algebraMap F E z * algebraMap F E (c * b) ∈ O` using `hz 0`.

Establish `hz2 : algebraMap F E z * algebraMap F E d₁ ∈ O` using `hz 1`. Use `⟨c * b * d₁ * z, by simp [hc, hb0, hd₁0, hz0], fun G hG => ?_⟩` and prove the remaining obligations. Establish `hG0 : _root_.GlobalTheory.HL.EichCont.Bd O (G 0 - A 0) (c * b)` using `Bd_of_Bd_mul_of_mem_O (o := d₁ * z) (Bd_of_eq (by ring) (hG 0)) (by rw [map_mul, mul_comm]; exact hz2)`. Establish `hGs : ∀ i : Fin r, _root_.GlobalTheory.HL.EichCont.Bd O (G i.succ - A i.succ) d₁` using `fun i => Bd_of_Bd_mul_of_mem_O (o := c * b * z) (Bd_of_eq (by ring) (hG i.succ)) (by rw [map_mul, mul_comm]; exact hz1)`. Establish `hrest` using `hd₁ (fun i => G i.succ) hGs`.

Establish `hGsb : _root_.GlobalTheory.HL.EichCont.Bd O (List.ofFn fun i => G i.succ).prod b⁻¹`. Establish `h1 : _root_.GlobalTheory.HL.EichCont.Bd O ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) b⁻¹` using `Bd_of_Bd_mul_of_mem_O (o := c * a * b * w * b) (Bd_of_eq (by field_simp) hrest) (by`. Use `O.mul_mem (O.mul_mem (O.mul_mem hwc haO) hbO) hbO` as an intermediate fact. Simplify using `only [map_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use the proof step `ring)`. Use `Bd_add' hAs h1` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]`. Establish `key : G 0 * (List.ofFn fun i => G i.succ).prod - A 0 * (List.ofFn fun i => A i.succ).prod = (G 0 - A 0) * (List.ofFn fun i => G i.succ).prod + A 0 * ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod)`.

Rewrite using `[sub_mul, mul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Use `Bd_add' ?_ ?_` and prove the remaining obligations. Conclude with `Bd_of_eq (by field_simp) (Bd_mul' hG0 hGsb)`.

Conclude with `Bd_of_Bd_mul_of_mem_O (o := b * w) (Bd_of_eq (by field_simp) (Bd_mul' hA0 hrest)) (by rw [map_mul]; exact O.mul_mem hbO hwO)`.
-/
private lemma exists_Bd_prod_sub_of_Bd_sub : ∀ (r : ℕ) (A : Fin r → Module.End E (Fin N → E)) (c : F),
    c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ G : Fin r → Module.End E (Fin N → E),
      (∀ i, _root_.GlobalTheory.HL.EichCont.Bd O (G i - A i) d) →
        _root_.GlobalTheory.HL.EichCont.Bd O ((List.ofFn G).prod - (List.ofFn A).prod) c := by
  intro r
  induction r with
  | zero =>
    intro A c _
    exact ⟨1, one_ne_zero, fun G _ => by
      simp only [List.ofFn_zero, List.prod_nil, sub_self]
      exact Bd_zero' c⟩
  | succ r ih =>
    intro A c hc
    obtain ⟨a, ha0, haO, hA0⟩ := exists_algebraMap_mem_O_Bd_inv hden (A 0)
    obtain ⟨b, hb0, hbO, hAs⟩ := exists_algebraMap_mem_O_Bd_inv hden (List.ofFn fun i => A i.succ).prod
    obtain ⟨w, hw0, hwO, hwc⟩ := hden (algebraMap F E c)
    obtain ⟨d₁, hd₁0, hd₁⟩ := ih (fun i => A i.succ) (c * a * b * w) (by simp [hc, ha0, hb0, hw0])
    obtain ⟨z, hz0, hzO, hz⟩ := exists_algebraMap_mul_mem_O_forall hden
      ![algebraMap F E (c * b), algebraMap F E d₁]
    have hz1 : algebraMap F E z * algebraMap F E (c * b) ∈ O := hz 0
    have hz2 : algebraMap F E z * algebraMap F E d₁ ∈ O := hz 1
    refine ⟨c * b * d₁ * z, by simp [hc, hb0, hd₁0, hz0], fun G hG => ?_⟩
    have hG0 : _root_.GlobalTheory.HL.EichCont.Bd O (G 0 - A 0) (c * b) :=
      Bd_of_Bd_mul_of_mem_O (o := d₁ * z) (Bd_of_eq (by ring) (hG 0))
        (by rw [map_mul, mul_comm]; exact hz2)
    have hGs : ∀ i : Fin r, _root_.GlobalTheory.HL.EichCont.Bd O (G i.succ - A i.succ) d₁ := fun i =>
      Bd_of_Bd_mul_of_mem_O (o := c * b * z) (Bd_of_eq (by ring) (hG i.succ))
        (by rw [map_mul, mul_comm]; exact hz1)
    have hrest := hd₁ (fun i => G i.succ) hGs
    have hGsb : _root_.GlobalTheory.HL.EichCont.Bd O (List.ofFn fun i => G i.succ).prod b⁻¹ := by
      have h1 : _root_.GlobalTheory.HL.EichCont.Bd O
          ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) b⁻¹ :=
        Bd_of_Bd_mul_of_mem_O (o := c * a * b * w * b) (Bd_of_eq (by field_simp) hrest) (by
          have := O.mul_mem (O.mul_mem (O.mul_mem hwc haO) hbO) hbO
          simp only [map_mul]
          convert this using 1
          ring)
      have := Bd_add' hAs h1
      rwa [add_sub_cancel] at this
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have key : G 0 * (List.ofFn fun i => G i.succ).prod - A 0 * (List.ofFn fun i => A i.succ).prod =
        (G 0 - A 0) * (List.ofFn fun i => G i.succ).prod +
          A 0 * ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) := by
      rw [sub_mul, mul_sub]
      abel
    rw [key]
    refine Bd_add' ?_ ?_
    · exact Bd_of_eq (by field_simp) (Bd_mul' hG0 hGsb)
    · exact Bd_of_Bd_mul_of_mem_O (o := b * w) (Bd_of_eq (by field_simp) (Bd_mul' hA0 hrest))
        (by rw [map_mul]; exact O.mul_mem hbO hwO)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L N r Hm X u s e he Λ hΛ c`. Establish `hden` using `exists_algebraMap_mul_mem_O L`. Take `⟨β, hβ0, hβO, hβ⟩` from `exists_algebraMap_mul_mem_O_forall hden (fun p : (Fin N × Fin N) ⊕ (Fin r × Fin N) => Sum.elim (fun q => Hm q.1 q.2) (fun q => X q.1 q.2) p)`. Establish `hH : ∀ i j, algebraMap F E β * Hm i j ∈ L.O` using `fun i j => hβ (Sum.inl (i, j))`. Establish `hX : ∀ i k, algebraMap F E β * X i k ∈ L.O` using `fun i k => hβ (Sum.inr (i, k))`.

Establish `hXc : ∀ i k, algebraMap F E β * L.cj (X i k) ∈ L.O` using `fun i k => by`. Use `_root_.GlobalTheory.UnramOrder.cj_mem L (hX i k)` as an intermediate fact. Rewrite `this` using `[map_mul, L.cj.commutes]`. Then use the resulting hypothesis. Establish `hform1 : ∀ v o : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o → algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v o ∈ L.O`. Introduce `v o hv ho`.

Unfold `_root_.GlobalTheory.HL.hf`. Rewrite using `[Finset.mul_sum]`. Use `L.O.sum_mem fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `L.O.sum_mem fun b _ => ?_` and prove the remaining obligations.

Use `L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (_root_.GlobalTheory.UnramOrder.cj_mem L (ho b))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hform2 : ∀ v : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → ∀ i, algebraMap F E β * algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v (X i) ∈ L.O`. Introduce `v hv i`.

Unfold `_root_.GlobalTheory.HL.hf`. Rewrite using `[Finset.mul_sum]`. Use `L.O.sum_mem fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `L.O.sum_mem fun b _ => ?_` and prove the remaining obligations.

Use `L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (hXc i b)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ v w w' : Fin N → E, _root_.GlobalTheory.HL.hf L Hm v w - _root_.GlobalTheory.HL.hf L Hm v w' = _root_.GlobalTheory.HL.hf L Hm v (w - w')`. Introduce `v w w'`.

Unfold `_root_.GlobalTheory.HL.hf`. Simplify using `only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]`. Establish `hsmul : ∀ (v o : Fin N → E) (t : F), _root_.GlobalTheory.HL.hf L Hm v (algebraMap F E t • o) = algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o`. Introduce `v o t`. Unfold `_root_.GlobalTheory.HL.hf`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hdiff : ∀ i (u₁ : Fin N → E) (s₁ : E) (t : F) (o : Fin N → E) (o' : E) (v : Fin N → E), u₁ - u i = algebraMap F E t • o → s₁ - s i = algebraMap F E t * o' → _root_.GlobalTheory.HL.eich L Hm (X i) u₁ s₁ v - _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v = algebraMap F E t • …`. Introduce `i u₁ s₁ t o o' v hu hs`.

Establish `hu' : u₁ = u i + algebraMap F E t • o` using `by rw [← hu]; abel`. Establish `hs' : s₁ = s i + algebraMap F E t * o'` using `by rw [← hs]; ring`. Establish `h1 : _root_.GlobalTheory.HL.hf L Hm v u₁ = _root_.GlobalTheory.HL.hf L Hm v (u i) + algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o`. Rewrite using `[← hsmul, ← hu, ← hsub]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `_root_.GlobalTheory.HL.eich`. Rewrite using `[h1, hu', hs']`. Use extensionality with `k`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbr : ∀ i (o : Fin N → E) (o' : E) (v : Fin N → E), _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o → o' ∈ L.O → _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E (β ^ 3) • (_root_.GlobalTheory.HL.hf L Hm v o • X i - _root_.GlobalThe …`. Introduce `i o o' v hv ho ho' k`. Establish `t1` using `L.O.mul_mem (L.O.mul_mem (hform1 v o hv ho) (hX i k)) hβO`. Establish `t2` using `L.O.mul_mem (L.O.mul_mem (hform2 v hv i) hβO) (ho k)`. Establish `t3` using `L.O.mul_mem (L.O.mul_mem (hform2 v hv i) ho') (hX i k)`.

Use `L.O.sub_mem t1 (L.O.add_mem t2 t3)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Set `φ : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* Module.End E (Fin N → E)` to `LinearEquiv.automorphismGroup.toLinearMapMonoidHom`.

Establish `hP : ∀ (f : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (y : Fin N → E), (List.ofFn f).prod y = (List.ofFn fun i => φ (f i)).prod y`. Introduce `f y`. Establish `: φ (List.ofFn f).prod = (List.ofFn fun i => φ (f i)).prod`. Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression.

Rewrite using `[← this]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨a, ha0, haO, ha⟩ : ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧ ∀ x ∈ Λ, _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E a • x) := by`. Take `⟨S, hS⟩` from `hΛ.1`. Take `⟨a, ha0, haO, haz⟩` from `exists_algebraMap_mul_mem_O_forall hden (fun p : S × Fin N => (p.1 : Fin N → E) p.2)`.

Use `⟨a, ha0, haO, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact fun j => haz (⟨y, hy⟩, j)`. Consider the case `zero => exact fun j => by simp`.

Consider the case `add y z _ _ hy hz => exact fun j => by simpa [mul_add] using L.O.add_mem (hy j) (hz j)`. Consider the case `smul o y _ hy`. Conclude with `fun j => by simpa [Subring.smul_def, mul_left_comm] using L.O.mul_mem o.2 (hy j)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb0, hbO, hb⟩ : ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ ∀ m, _root_.GlobalTheory.HL.EichCont.IntV L.O m → algebraMap F E b • m ∈ Λ := by`. Establish `hstep : ∀ w ∈ Submodule.span E (Λ : Set (Fin N → E)), ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ algebraMap F E b • w ∈ Λ`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨b₁, h₁0, h₁O, h₁⟩` from `hy`. Take `⟨b₂, h₂0, h₂O, h₂⟩` from `hz`. Use `⟨b₁ * b₂, mul_ne_zero h₁0 h₂0, by rw [map_mul]; exact L.O.mul_mem h₁O h₂O, ?_⟩` and prove the remaining obligations. Establish `e1` using `Λ.smul_mem (⟨algebraMap F E b₂, h₂O⟩ : L.O) h₁`. Establish `e2` using `Λ.smul_mem (⟨algebraMap F E b₁, h₁O⟩ : L.O) h₂`.

Use `Λ.add_mem e1 e2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subring.smul_def, smul_smul, map_mul, smul_add, mul_comm]`. Consider the case `smul t y _ hy`. Take `⟨b₁, h₁0, h₁O, h₁⟩` from `hy`.

Take `⟨w₁, hw0, hwO, hwt⟩` from `hden t`. Use `⟨w₁ * b₁, mul_ne_zero hw0 h₁0, by rw [map_mul]; exact L.O.mul_mem hwO h₁O, ?_⟩` and prove the remaining obligations. Establish `e1` using `Λ.smul_mem (⟨algebraMap F E w₁ * t, hwt⟩ : L.O) h₁`. Use `e1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Subring.smul_def, smul_smul, smul_smul, map_mul]`.

Use `congr 1`. Use `show _ = algebraMap F E w₁ * t * algebraMap F E b₁`. Expand and normalize the polynomial expressions, which then agree. Use `choose bj hbj0 hbjO hbj using fun j : Fin N => hstep (fun k => if j = k then (1 : E) else 0) (by rw [hΛ.2]; exact Submodule.mem_top)`. Use `⟨∏ j, bj j, Finset.prod_ne_zero_iff.2 fun j _ => hbj0 j, by rw [map_prod]; exact L.O.prod_mem fun j _ => hbjO j, fun m hm => ?_⟩` and prove the remaining obligations.

Establish `hej : ∀ j, algebraMap F E (∏ k, bj k) • (fun k => if j = k then (1 : E) else 0) ∈ Λ`. Introduce `j`. Establish `hO' : algebraMap F E (∏ k ∈ Finset.univ.erase j, bj k) ∈ L.O`. Rewrite using `[map_prod]`. Conclude with `L.O.prod_mem fun k _ => hbjO k`.

Use `Λ.smul_mem (⟨_, hO'⟩ : L.O) (hbj j)` as an intermediate fact. Rewrite `this` using `[Subring.smul_def, smul_smul, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]`. Then use the resulting hypothesis. Rewrite using `[pi_eq_sum_univ m, Finset.smul_sum]`. Use `Λ.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `Λ.smul_mem (⟨m j, hm j⟩ : L.O) (hej j)`. Take `⟨γ, hγ0, -, hγ⟩` from `exists_algebraMap_mem_O_Bd_inv hden ((List.ofFn e).prod.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)).toLinearMap`. Take `⟨d₀, hd₀0, hd₀⟩` from `exists_Bd_prod_sub_of_Bd_sub hden r (fun i => φ (e i)) ((c : F) * b * a * γ) (by simp [hb0, ha0, hγ0])`. Use `⟨Units.mk0 (d₀ * β ^ 3) (by simp [hd₀0, hβ0]), fun u' s' e' he' hu' hs' x hx => ?_⟩` and prove the remaining obligations. Use `choose ou hou hueq using hu'`.

Use `choose os hos hseq using hs'`. Establish `hfac : ∀ i, _root_.GlobalTheory.HL.EichCont.Bd L.O (φ (e' i) - φ (e i)) d₀`. Introduce `i m hm`. Use `⟨_, hbr i (ou i) (os i) m hm (fun j => hou i j) (hos i), ?_⟩` and prove the remaining obligations. Use `hdiff i (u' i) (s' i) (d₀ * β ^ 3) (ou i) (os i) m (funext fun j => by rw [Pi.sub_apply, hueq i j, Units.val_mk0]; rfl) (by rw [hseq i, Units.val_mk0])` as an intermediate fact.

Use `show e' i m - e i m = _`. Rewrite using `[he', he, this, smul_smul, ← map_mul]`. Take `⟨m₁, hm₁, e₁⟩` from `hd₀ (fun i => φ (e' i)) hfac _ (ha x hx)`. Take `⟨m₂, hm₂, e₂⟩` from `hγ m₁ hm₁`. Establish `e₂' : ((List.ofFn e).prod).symm m₁ = algebraMap F E γ⁻¹ • m₂` using `e₂`.

Use `⟨algebraMap F E b • m₂, hb m₂ hm₂, ?_⟩` and prove the remaining obligations. Establish `hx' : (List.ofFn e').prod x - (List.ofFn e).prod x = algebraMap F E a⁻¹ • (algebraMap F E ((c : F) * b * a * γ) • m₁)`. Rewrite using `[← e₁, LinearMap.sub_apply, ← hP e', ← hP e, map_smul, map_smul, ← smul_sub, smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sub, LinearEquiv.symm_apply_apply]`.

Use `_ = algebraMap F E (c : F) • algebraMap F E b • m₂ := by`. Rewrite using `[hx', smul_smul, ← map_mul, map_smul, e₂', smul_smul, ← map_mul, smul_smul, ← map_mul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.
-/
theorem _root_.GlobalTheory.HL.EichCont.prod_eich_cont : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E)
    (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (he : ∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v)
    (Λ : Submodule L.O (Fin N → E)) (hΛ : _root_.GlobalTheory.HL.IsLat L Λ) (c : Fˣ),
    ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E)
      (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)),
      (∀ i v, e' i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u' i) (s' i) v) →
      (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) →
      (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) →
      ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x =
        algebraMap F E c • y := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm X u s e he Λ hΛ c
  have hden := exists_algebraMap_mul_mem_O L
  obtain ⟨β, hβ0, hβO, hβ⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : (Fin N × Fin N) ⊕ (Fin r × Fin N) =>
      Sum.elim (fun q => Hm q.1 q.2) (fun q => X q.1 q.2) p)
  have hH : ∀ i j, algebraMap F E β * Hm i j ∈ L.O := fun i j => hβ (Sum.inl (i, j))
  have hX : ∀ i k, algebraMap F E β * X i k ∈ L.O := fun i k => hβ (Sum.inr (i, k))
  have hXc : ∀ i k, algebraMap F E β * L.cj (X i k) ∈ L.O := fun i k => by
    have := _root_.GlobalTheory.UnramOrder.cj_mem L (hX i k)
    rwa [map_mul, L.cj.commutes] at this

  have hform1 : ∀ v o : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o →
      algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v o ∈ L.O := by
    intro v o hv ho
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (_root_.GlobalTheory.UnramOrder.cj_mem L (ho b))
    convert this using 1
    ring
  have hform2 : ∀ v : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → ∀ i,
      algebraMap F E β * algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v (X i) ∈ L.O := by
    intro v hv i
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (hXc i b)
    convert this using 1
    ring
  have hsub : ∀ v w w' : Fin N → E, _root_.GlobalTheory.HL.hf L Hm v w -
      _root_.GlobalTheory.HL.hf L Hm v w' = _root_.GlobalTheory.HL.hf L Hm v (w - w') := by
    intro v w w'
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmul : ∀ (v o : Fin N → E) (t : F), _root_.GlobalTheory.HL.hf L Hm v
      (algebraMap F E t • o) = algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
    intro v o t
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiff : ∀ i (u₁ : Fin N → E) (s₁ : E) (t : F) (o : Fin N → E) (o' : E) (v : Fin N → E),
      u₁ - u i = algebraMap F E t • o → s₁ - s i = algebraMap F E t * o' →
      _root_.GlobalTheory.HL.eich L Hm (X i) u₁ s₁ v - _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v =
        algebraMap F E t • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
          _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i)) := by
    intro i u₁ s₁ t o o' v hu hs
    have hu' : u₁ = u i + algebraMap F E t • o := by rw [← hu]; abel
    have hs' : s₁ = s i + algebraMap F E t * o' := by rw [← hs]; ring
    have h1 : _root_.GlobalTheory.HL.hf L Hm v u₁ = _root_.GlobalTheory.HL.hf L Hm v (u i) +
        algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
      rw [← hsmul, ← hu, ← hsub]; ring
    unfold _root_.GlobalTheory.HL.eich
    rw [h1, hu', hs']
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbr : ∀ i (o : Fin N → E) (o' : E) (v : Fin N → E), _root_.GlobalTheory.HL.EichCont.IntV L.O v →
      _root_.GlobalTheory.HL.EichCont.IntV L.O o → o' ∈ L.O →
      _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E (β ^ 3) • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
        _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i))) := by
    intro i o o' v hv ho ho' k
    have t1 := L.O.mul_mem (L.O.mul_mem (hform1 v o hv ho) (hX i k)) hβO
    have t2 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) hβO) (ho k)
    have t3 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) ho') (hX i k)
    have := L.O.sub_mem t1 (L.O.add_mem t2 t3)
    convert this using 1
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_pow]
    ring
  let φ : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* Module.End E (Fin N → E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hP : ∀ (f : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (y : Fin N → E),
      (List.ofFn f).prod y = (List.ofFn fun i => φ (f i)).prod y := by
    intro f y
    have : φ (List.ofFn f).prod = (List.ofFn fun i => φ (f i)).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [← this]; rfl
  obtain ⟨a, ha0, haO, ha⟩ : ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧
      ∀ x ∈ Λ, _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E a • x) := by
    obtain ⟨S, hS⟩ := hΛ.1
    obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
      (fun p : S × Fin N => (p.1 : Fin N → E) p.2)
    refine ⟨a, ha0, haO, fun x hx => ?_⟩
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun j => haz (⟨y, hy⟩, j)
    | zero => exact fun j => by simp
    | add y z _ _ hy hz => exact fun j => by simpa [mul_add] using L.O.add_mem (hy j) (hz j)
    | smul o y _ hy =>
      exact fun j => by simpa [Subring.smul_def, mul_left_comm] using L.O.mul_mem o.2 (hy j)
  obtain ⟨b, hb0, hbO, hb⟩ : ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧
      ∀ m, _root_.GlobalTheory.HL.EichCont.IntV L.O m → algebraMap F E b • m ∈ Λ := by
    have hstep : ∀ w ∈ Submodule.span E (Λ : Set (Fin N → E)),
        ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ algebraMap F E b • w ∈ Λ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simpa using hy⟩
      | zero => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨b₂, h₂0, h₂O, h₂⟩ := hz
        refine ⟨b₁ * b₂, mul_ne_zero h₁0 h₂0, by rw [map_mul]; exact L.O.mul_mem h₁O h₂O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E b₂, h₂O⟩ : L.O) h₁
        have e2 := Λ.smul_mem (⟨algebraMap F E b₁, h₁O⟩ : L.O) h₂
        have := Λ.add_mem e1 e2
        convert this using 1
        simp only [Subring.smul_def, smul_smul, map_mul, smul_add, mul_comm]
      | smul t y _ hy =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨w₁, hw0, hwO, hwt⟩ := hden t
        refine ⟨w₁ * b₁, mul_ne_zero hw0 h₁0, by rw [map_mul]; exact L.O.mul_mem hwO h₁O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E w₁ * t, hwt⟩ : L.O) h₁
        convert e1 using 1
        rw [Subring.smul_def, smul_smul, smul_smul, map_mul]
        congr 1
        show _ = algebraMap F E w₁ * t * algebraMap F E b₁
        ring
    choose bj hbj0 hbjO hbj using fun j : Fin N =>
      hstep (fun k => if j = k then (1 : E) else 0) (by rw [hΛ.2]; exact Submodule.mem_top)
    refine ⟨∏ j, bj j, Finset.prod_ne_zero_iff.2 fun j _ => hbj0 j,
      by rw [map_prod]; exact L.O.prod_mem fun j _ => hbjO j, fun m hm => ?_⟩
    have hej : ∀ j, algebraMap F E (∏ k, bj k) • (fun k => if j = k then (1 : E) else 0) ∈ Λ := by
      intro j
      have hO' : algebraMap F E (∏ k ∈ Finset.univ.erase j, bj k) ∈ L.O := by
        rw [map_prod]; exact L.O.prod_mem fun k _ => hbjO k
      have := Λ.smul_mem (⟨_, hO'⟩ : L.O) (hbj j)
      rwa [Subring.smul_def, smul_smul, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at this
    rw [pi_eq_sum_univ m, Finset.smul_sum]
    refine Λ.sum_mem fun j _ => ?_
    rw [smul_comm]
    exact Λ.smul_mem (⟨m j, hm j⟩ : L.O) (hej j)
  obtain ⟨γ, hγ0, -, hγ⟩ := exists_algebraMap_mem_O_Bd_inv hden
    ((List.ofFn e).prod.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)).toLinearMap
  obtain ⟨d₀, hd₀0, hd₀⟩ := exists_Bd_prod_sub_of_Bd_sub hden r (fun i => φ (e i))
    ((c : F) * b * a * γ) (by simp [hb0, ha0, hγ0])
  refine ⟨Units.mk0 (d₀ * β ^ 3) (by simp [hd₀0, hβ0]), fun u' s' e' he' hu' hs' x hx => ?_⟩
  choose ou hou hueq using hu'
  choose os hos hseq using hs'
  have hfac : ∀ i, _root_.GlobalTheory.HL.EichCont.Bd L.O (φ (e' i) - φ (e i)) d₀ := by
    intro i m hm
    refine ⟨_, hbr i (ou i) (os i) m hm (fun j => hou i j) (hos i), ?_⟩
    have := hdiff i (u' i) (s' i) (d₀ * β ^ 3) (ou i) (os i) m
      (funext fun j => by rw [Pi.sub_apply, hueq i j, Units.val_mk0]; rfl)
      (by rw [hseq i, Units.val_mk0])
    show e' i m - e i m = _
    rw [he', he, this, smul_smul, ← map_mul]
  obtain ⟨m₁, hm₁, e₁⟩ := hd₀ (fun i => φ (e' i)) hfac _ (ha x hx)
  obtain ⟨m₂, hm₂, e₂⟩ := hγ m₁ hm₁
  have e₂' : ((List.ofFn e).prod).symm m₁ = algebraMap F E γ⁻¹ • m₂ := e₂
  refine ⟨algebraMap F E b • m₂, hb m₂ hm₂, ?_⟩
  have hx' : (List.ofFn e').prod x - (List.ofFn e).prod x = algebraMap F E a⁻¹ •
      (algebraMap F E ((c : F) * b * a * γ) • m₁) := by
    rw [← e₁, LinearMap.sub_apply, ← hP e', ← hP e, map_smul, map_smul, ← smul_sub, smul_smul,
      ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]
  calc ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x
      = ((List.ofFn e).prod).symm ((List.ofFn e').prod x - (List.ofFn e).prod x) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]
    _ = algebraMap F E (c : F) • algebraMap F E b • m₂ := by
        rw [hx', smul_smul, ← map_mul, map_smul, e₂', smul_smul, ← map_mul, smul_smul, ← map_mul]
        congr 2
        field_simp

end GlobalTheory.HL.EichCont
