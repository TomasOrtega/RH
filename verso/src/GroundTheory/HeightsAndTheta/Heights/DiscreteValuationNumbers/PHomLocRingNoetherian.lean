import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HomLocRingNoetherian

variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

/- English proof (translation)
Set `_` to `weightedGradedAlgebra R (blockWeight ι)`. Establish `hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs`. Use `DirectSum.coe_decompose_mul_add_of_left_mem (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem` as an intermediate fact. Rewrite using `[← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d), ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]`. Conclude with `this`.
-/
theorem component_form_mul {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  have hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem
  rw [← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d),
    ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]
  exact this

variable (P : Ideal (MRing ι R)) [P.IsPrime]

abbrev img : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P}

omit [DecidableEq K] in

/- English proof (translation)
Simplify using `[img, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem img_eq_zero_iff {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by
  simp [img, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Rewrite `huv`, the goal using `[← sub_eq_zero, ← map_sub, img_eq_zero_iff]`. Rewrite using `[← map_sub]`. Conclude with `hP _ huv d`.
-/
theorem img_component_congr (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by
  rw [← sub_eq_zero, ← map_sub, img_eq_zero_iff] at huv ⊢
  rw [← map_sub]
  exact hP _ huv d

omit [DecidableEq K] in

/- English proof (translation)
Introduce `h0` and use `ht (hPW (img_eq_zero_iff.mp h0))`.
-/
theorem img_ne_zero {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := fun h0 => ht (hPW (img_eq_zero_iff.mp h0))

/- English proof (translation)
The claim follows from `Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩`.
-/
theorem quot_mem {W : Ideal (MRing ι R)} {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hgW : g ∉ W) : img P f / img P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

end HomLocRingNoetherian

open HomLocRingNoetherian in

/- English proof (translation)
Introduce `R _ _ K _ _ ι _ P W _ hP hW _ hPW`. Use `set S := MRing ι R`. Use `set D := S ⧸ P`. Use `set F := FractionRing D`. Set `T : Submonoid S` to `{ carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W} one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩ mul_mem' := fun {a b} ha hb => ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }`.

Set `T' : Submonoid D` to `T.map (Ideal.Quotient.mk P)`. Establish `hT' : T' ≤ nonZeroDivisors D`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h0`.

Set `B : Subalgebra D F` to `Localization.subalgebra F T' hT'`. Establish `: IsNoetherianRing B` using `IsLocalization.isNoetherianRing T' B inferInstance`. Establish `rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h`. Introduce and unpack `y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩`. Take `⟨h, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Conclude with `⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩`. Establish `hAB : ∀ x ∈ homLocRing P W, x ∈ B`. Introduce `x hx`. Use `(Subring.closure_le (t := B.toSubring)).mpr ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨b, f, g, hf, hg, hgW, rfl⟩`.

Conclude with `⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩, by rw [IsFractionRing.mk'_eq_div]⟩`. Set `j : homLocRing P W →+* B` to `{ toFun := fun a => ⟨a, hAB a a.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I`. Introduce `I z hz`. Set `Q : F → Prop` to `fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W → y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W → ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t`.

Establish `Q0 : Q 0`. Introduce `s e h _ _ hy d t _ _`. Use `⟨0, I.zero_mem, ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[zero_mul, eq_comm, img_eq_zero_iff]`. Rewrite using `[img_eq_zero_iff.mpr (hP h hy d), zero_div]`.

Both sides reduce to the same expression. Establish `Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂)`. Introduce `y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW`. Take `⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩` from `rep y₁ hy₁`. Take `⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩` from `rep y₂ hy₂`.

Establish `hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂)` using `(hs.mul ht₁).mul ht₂`. Establish `hσW : s * t₁ * t₂ ∉ W` using `hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W`. Establish `hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d)` using `(ht₁.mul ht₂).mul ht`. Establish `hτW : t₁ * t₂ * t ∉ W` using `hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW`. Take `⟨a₁, ha₁I, ha₁⟩` from `Q₁ _ _ (h₁ * (s * t₂)) hσ hσW (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW`.

Take `⟨a₂, ha₂I, ha₂⟩` from `Q₂ _ _ (h₂ * (s * t₁)) hσ hσW (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW`. Use `⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩` and prove the remaining obligations. Establish `hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h)`. Simplify using `only [map_mul, map_add]`. Rewrite using `[← hb₁, ← hb₂, ← hy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `img_component_congr hP hsum ((e₁ + e₂) + d)`. Rewrite `hc` using `[component_form_mul (ht₁.mul ht₂), map_add, map_add]`. Establish `h1` using `img_ne_zero hPW ht₁W`. Establish `h2` using `img_ne_zero hPW ht₂W`.

Establish `h3` using `img_ne_zero hPW htW`. Rewrite using `[Subring.coe_add, ha₁, ha₂, ← add_div, hc]`. Simplify using `only [map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F))`.

Introduce `b hb a haI s e h hs hsW hy d t ht htW`. Take `⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩` from `rep b hb`. Take `⟨c, f, g, hf, hg, hgW, hfg⟩` from `(hmem R K ι P W hW hPW a).mp a.2`. Establish `hfg' : (a : F) = img P f / img P g` using `hfg`. Establish `hg0` using `img_ne_zero hPW hgW`.

Establish `hfa : img P f = a * img P g` using `by rw [hfg', div_mul_cancel₀ _ hg0]`. Establish `hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h)`. Simplify using `only [map_mul]`. Rewrite using `[hfa, ← hy, ← hb₁]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc` using `img_component_congr hP hrel (c + (d + e₁))`. Rewrite `hc` using `[component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel, component_form_mul (ht₁.mul hg)]`. Establish `ha'` using `quot_mem (P := P) (W := W) (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁) (hW.mul_notMem htW ht₁W)`. Use `⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩` and prove the remaining obligations. Establish `h1` using `img_ne_zero hPW ht₁W`.

Establish `h3` using `img_ne_zero hPW htW`. Rewrite using `[Subring.coe_mul, hfg']`. Simplify using `only [map_mul] at hc ⊢`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hc`.

Establish `hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F))`. Introduce `y hy`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨a, haI, rfl⟩ b`. Conclude with `Qgen b b.2 a haI`.

Introduce `b`. Simplify using `using Q0`. Introduce `y₁ y₂ _ _ Q₁ Q₂ b`. Use `Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)` as an intermediate fact. Simplify `this` using `[mul_add]`.

Introduce `c y _ Qy b`. Use `Qy (b * c)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Take `⟨c, f, g, hf, hg, hgW, hfg⟩` from `(hmem R K ι P W hW hPW z).mp z.2`. Establish `hfg' : (z : F) = img P f / img P g` using `hfg`.

Establish `hg0` using `img_ne_zero hPW hgW`. Take `⟨a, haI, ha⟩` from `hspan _ hz 1 g c f hg hgW (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0]) c g hg hgW`. Rewrite `ha` using `[hf.weightedHomogeneousComponent_same, ← hfg']`. Conclude with `(Subtype.ext ha : a = z) ▸ haI`. Establish `hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j)`.

Introduce `I₁ I₂ h12`. Establish `e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I` using `fun I => le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map`. Rewrite using `[← e I₁, ← e I₂]`. Conclude with `congrArg (Ideal.comap j) h12`. Establish `hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j)` using `fun _ _ h => Ideal.map_mono h`.

Establish `hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j)` using `hmono'.strictMono_of_injective hinj`. Establish `: WellFoundedGT (Ideal B)` using `isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)`. Conclude with `isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)`.
-/
theorem HomLocRingNoetherian.proof (hmem : HomLocRingMem.Statement.{u}) :
    HomLocRingNoetherian.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W _ hP hW _ hPW
  classical
  set S := MRing ι R
  set D := S ⧸ P
  set F := FractionRing D

  let T : Submonoid S :=
    { carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W}
      one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }
  let T' : Submonoid D := T.map (Ideal.Quotient.mk P)
  have hT' : T' ≤ nonZeroDivisors D := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  let B : Subalgebra D F := Localization.subalgebra F T' hT'
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing T' B inferInstance

  have rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h := by
    rintro y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩
  have hAB : ∀ x ∈ homLocRing P W, x ∈ B := by
    intro x hx
    refine (Subring.closure_le (t := B.toSubring)).mpr ?_ hx
    rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div]⟩
  let j : homLocRing P W →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I := by
    intro I z hz
    let Q : F → Prop := fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W →
      y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W →
        ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t
    have Q0 : Q 0 := by
      intro s e h _ _ hy d t _ _
      refine ⟨0, I.zero_mem, ?_⟩
      rw [zero_mul, eq_comm, img_eq_zero_iff] at hy
      rw [img_eq_zero_iff.mpr (hP h hy d), zero_div]
      rfl
    have Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂) := by
      intro y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep y₁ hy₁
      obtain ⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩ := rep y₂ hy₂
      have hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂) := (hs.mul ht₁).mul ht₂
      have hσW : s * t₁ * t₂ ∉ W := hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W
      have hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d) := (ht₁.mul ht₂).mul ht
      have hτW : t₁ * t₂ * t ∉ W := hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW
      obtain ⟨a₁, ha₁I, ha₁⟩ := Q₁ _ _ (h₁ * (s * t₂)) hσ hσW
        (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW
      obtain ⟨a₂, ha₂I, ha₂⟩ := Q₂ _ _ (h₂ * (s * t₁)) hσ hσW
        (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW
      refine ⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩
      have hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h) := by
        simp only [map_mul, map_add]; rw [← hb₁, ← hb₂, ← hy]; ring
      have hc := img_component_congr hP hsum ((e₁ + e₂) + d)
      rw [component_form_mul (ht₁.mul ht₂), map_add, map_add] at hc
      have h1 := img_ne_zero hPW ht₁W
      have h2 := img_ne_zero hPW ht₂W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_add, ha₁, ha₂, ← add_div, hc]
      simp only [map_mul]
      field_simp
    have Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F)) := by
      intro b hb a haI s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep b hb
      obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW a).mp a.2
      have hfg' : (a : F) = img P f / img P g := hfg
      have hg0 := img_ne_zero hPW hgW
      have hfa : img P f = a * img P g := by rw [hfg', div_mul_cancel₀ _ hg0]
      have hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h) := by
        simp only [map_mul]; rw [hfa, ← hy, ← hb₁]; ring
      have hc := img_component_congr hP hrel (c + (d + e₁))
      rw [component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel,
        component_form_mul (ht₁.mul hg)] at hc
      have ha' := quot_mem (P := P) (W := W)
        (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁)
        (hW.mul_notMem htW ht₁W)
      refine ⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩
      have h1 := img_ne_zero hPW ht₁W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_mul, hfg']
      simp only [map_mul] at hc ⊢
      field_simp
      linear_combination hc
    have hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F)) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, haI, rfl⟩ b
        exact Qgen b b.2 a haI
      · intro b
        simpa using Q0
      · intro y₁ y₂ _ _ Q₁ Q₂ b
        have := Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)
        simpa [mul_add] using this
      · intro c y _ Qy b
        have := Qy (b * c)
        simpa [mul_assoc] using this
    obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW z).mp z.2
    have hfg' : (z : F) = img P f / img P g := hfg
    have hg0 := img_ne_zero hPW hgW
    obtain ⟨a, haI, ha⟩ := hspan _ hz 1 g c f hg hgW
      (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0])
      c g hg hgW
    rw [hf.weightedHomogeneousComponent_same, ← hfg'] at ha
    exact (Subtype.ext ha : a = z) ▸ haI
  have hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j) := by
    intro I₁ I₂ h12
    have e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I := fun I =>
      le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map
    rw [← e I₁, ← e I₂]
    exact congrArg (Ideal.comap j) h12
  have hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j) := fun _ _ h => Ideal.map_mono h
  have hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j) :=
    hmono'.strictMono_of_injective hinj
  have : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
