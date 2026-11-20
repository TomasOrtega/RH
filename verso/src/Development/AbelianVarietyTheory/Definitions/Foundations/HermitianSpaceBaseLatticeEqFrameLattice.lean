import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

section Lattice

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable (E) in

def intLoc (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) where
  carrier := AddSubgroup.closure {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, z = a ⊗ₜ[F] (x : E)}
  zero_mem' := zero_mem _
  add_mem' := add_mem
  neg_mem' := neg_mem
  one_mem' := AddSubgroup.subset_closure ⟨1, one_mem _, 1, rfl⟩
  mul_mem' := by
    intro y z hy hz
    induction hy, hz using AddSubgroup.closure_induction₂ with
    | mem y z hy hz =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      obtain ⟨b, hb, x', rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, x * x', by simp⟩
    | zero_left => rw [zero_mul]; exact zero_mem _
    | zero_right => rw [mul_zero]; exact zero_mem _
    | add_left _ _ _ _ _ _ h h' => rw [add_mul]; exact add_mem h h'
    | add_right _ _ _ _ _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg_left _ _ _ _ h => rw [neg_mul]; exact neg_mem h
    | neg_right _ _ _ _ h => rw [mul_neg]; exact neg_mem h

variable {F}

omit [NumberField E] in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩`.
-/
theorem tmul_mem_intLoc {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    a ⊗ₜ[F] (x : E) ∈ intLoc F E v := AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy => obtain ⟨a, ha, x, rfl⟩ := hy`. Conclude with `h1 a ha x`. Consider the case `zero => exact h0`. Consider the case `add y z _ _ hy hz => exact hadd y z hy hz`.

Consider the case `neg y _ hy => exact hneg y hy`.
-/
theorem intLoc_induction {v : HeightOneSpectrum (𝓞 F)} {p : Fv F v ⊗[F] E → Prop}
    (h1 : ∀ a ∈ v.adicCompletionIntegers F, ∀ x : 𝓞 E, p (a ⊗ₜ[F] (x : E))) (h0 : p 0)
    (hadd : ∀ y z, p y → p z → p (y + z)) (hneg : ∀ y, p y → p (-y)) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    p y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy => obtain ⟨a, ha, x, rfl⟩ := hy; exact h1 a ha x
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | neg y _ hy => exact hneg y hy

/- English proof (translation)
The claim follows from `intLoc_induction (p := fun y => absFin F v y ≤ 1) (fun a ha x => (absFin_tmul_le F v a x).trans (by exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 ha)) (by simp) (fun y z hy hz => (absFin_add_le F v y z).trans (max_le hy hz)) (fun y hy => by rwa [absFin_neg]) hy`.
-/
theorem absFin_le_one_of_mem_intLoc {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    absFin F v y ≤ 1 :=
  intLoc_induction (p := fun y => absFin F v y ≤ 1)
    (fun a ha x => (absFin_tmul_le F v a x).trans (by exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 ha))
    (by simp) (fun y z hy hz => (absFin_add_le F v y z).trans (max_le hy hz))
    (fun y hy => by rwa [absFin_neg]) hy

omit [NumberField E] in
/- English proof (translation)
The claim follows from `intLoc_induction (p := fun y => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y ∈ intLoc F E v) (fun _ ha x => tmul_mem_intLoc ha (RingOfIntegers.mapRingHom (σ : E →+* E) x)) (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw …`.
-/
theorem sigR_mem_intLoc (σ : E →ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y ∈ intLoc F E v :=
  intLoc_induction (p := fun y => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y ∈ intLoc F E v)
    (fun _ ha x => tmul_mem_intLoc ha (RingOfIntegers.mapRingHom (σ : E →+* E) x))
    (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
    (fun y hy => by rw [map_neg]; exact neg_mem hy) hy

variable (F) in

def latLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) where
  carrier := AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' := by
    rintro ⟨c, hc⟩ y hy
    change c • y ∈ AddSubgroup.closure _
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, x', hx', rfl⟩ := hz
      refine intLoc_induction (p := fun c => c • (fun i => b ⊗ₜ[F] x' i) ∈ AddSubgroup.closure _) (fun a ha x => ?_)
        (by rw [zero_smul]; exact zero_mem _) (fun _ _ h h' => by rw [add_smul]; exact add_mem h h')
        (fun _ h => by rw [neg_smul]; exact neg_mem h) hc
      refine AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, x • x', L.smul_mem x hx', funext fun i => ?_⟩
      exact Algebra.TensorProduct.tmul_mul_tmul a b (x : E) (x' i)
    | zero => rw [smul_zero]; exact zero_mem _
    | add _ _ _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg _ _ h => rw [smul_neg]; exact neg_mem h

omit [NumberField E] in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩`.
-/
theorem tmul_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ L) :
    (fun i => a ⊗ₜ[F] x i) ∈ latLoc F L v := AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy => obtain ⟨a, ha, x, hx, rfl⟩ := hy`. Conclude with `h1 a ha x hx`. Consider the case `zero => exact h0`. Consider the case `add y z _ _ hy hz => exact hadd y z hy hz`.

Consider the case `neg y _ hy => exact hneg y hy`.
-/
theorem latLoc_induction {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}
    {p : (Fin n → Fv F v ⊗[F] E) → Prop}
    (h1 : ∀ a ∈ v.adicCompletionIntegers F, ∀ x ∈ L, p (fun i => a ⊗ₜ[F] x i)) (h0 : p 0)
    (hadd : ∀ y z, p y → p z → p (y + z)) (hneg : ∀ y, p y → p (-y)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc F L v) : p y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy => obtain ⟨a, ha, x, hx, rfl⟩ := hy; exact h1 a ha x hx
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | neg y _ hy => exact hneg y hy

variable (E n) in

abbrev stdLattice : Submodule (𝓞 E) (Fin n → E) := Formalism.UG.stdLat (𝓞 E)

omit [NumberField E] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `latLoc_induction (p := fun y => ∀ i, y i ∈ intLoc F E v) (fun a ha x hx i => ?_) (fun _ => zero_mem _) (fun y z hy hz i => add_mem (hy i) (hz i)) (fun y hy i => neg_mem (hy i))` and prove the remaining obligations. Take `⟨r, hr⟩` from `hx i trivial`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] x i ∈ _`. Rewrite using `[← hr]`.

Conclude with `tmul_mem_intLoc ha r`. Introduce `h`. Rewrite using `[← Finset.univ_sum_single y]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n` using `fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by`.

Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e]⟩`. Establish `h2` using `(latLoc F (stdLattice E n) v).smul_mem ⟨y i, h i⟩ (tmul_mem_latLoc (one_mem _) h1)`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `_ = y i * ((1 : Fv F v) ⊗ₜ[F] (Pi.single i 1 : Fin n → E) j)`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality.

Simplify using `[← Algebra.TensorProduct.one_def]`. Simplify using `[e]`.
-/
theorem mem_latLoc_stdLattice {v : HeightOneSpectrum (𝓞 F)} {y : Fin n → Fv F v ⊗[F] E} :
    y ∈ latLoc F (stdLattice E n) v ↔ ∀ i, y i ∈ intLoc F E v := by
  constructor
  · refine latLoc_induction (p := fun y => ∀ i, y i ∈ intLoc F E v) (fun a ha x hx i => ?_) (fun _ => zero_mem _)
      (fun y z hy hz i => add_mem (hy i) (hz i)) (fun y hy i => neg_mem (hy i))
    obtain ⟨r, hr⟩ := hx i trivial
    change a ⊗ₜ[F] x i ∈ _
    rw [← hr]
    exact tmul_mem_intLoc ha r
  · intro h
    rw [← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n := fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
      by_cases e : j = i
      · subst e; simp
      · simp [e]⟩
    have h2 := (latLoc F (stdLattice E n) v).smul_mem ⟨y i, h i⟩ (tmul_mem_latLoc (one_mem _) h1)
    convert h2 using 1
    funext j
    change _ = y i * ((1 : Fv F v) ⊗ₜ[F] (Pi.single i 1 : Fin n → E) j)
    by_cases e : j = i
    · subst e; simp [← Algebra.TensorProduct.one_def]
    · simp [e]

def vecLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Af F ⊗[F] E) : Fin n → Fv F v ⊗[F] E :=
  fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy v`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`.

Conclude with `tmul_mem_latLoc (ha v) hx`. Consider the case `zero`. Establish `: vecLoc v (0 : Fin n → Af F ⊗[F] E) = 0` using `funext fun i => map_zero _`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz`. Establish `: vecLoc v (y + z) = vecLoc v y + vecLoc v z` using `funext fun i => map_add _ _ _`. Rewrite using `[this]`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy`.

Establish `: vecLoc v (-y) = -vecLoc v y` using `funext fun i => map_neg _ _`. Rewrite using `[this]`. Conclude with `neg_mem hy`. Introduce `h`. Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hL`.

Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Take `⟨k, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`. Establish `hx : ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • (s j : Fin n → E)` using `fun w hw => by`. Establish `: (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨m, hm⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 this`.

Conclude with `⟨m, by simpa using (congrArg Subtype.val hm).symm⟩`. Establish `hc : ∀ v, ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧ ∀ i, vecLoc v y i = ∑ j, a j ⊗ₜ[F] (s j : Fin n → E) i` using `fun v => by`. Use `latLoc_induction (p := fun y => ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧ ∀ i, y i = ∑ j, a j ⊗ₜ[F] (s j : Fin n → E) i) ?_ ⟨0, fun _ => zero_mem _, fun i => by simp⟩ ?_ ?_ (h v)` and prove the remaining obligations. Introduce `a ha w hw`. Take `⟨m, rfl⟩` from `hx w hw`.

Use `⟨fun j => m j • a, fun j => zsmul_mem ha _, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => (TensorProduct.smul_tmul _ _ _).symm`. Introduce and unpack `y z ⟨a, ha, ea⟩ ⟨b, hb, eb⟩`. Conclude with `⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by`.

Simplify using `only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩`. Introduce and unpack `y ⟨a, ha, ea⟩`. Conclude with `⟨-a, fun j => neg_mem (ha j), fun i => by`. Simplify using `only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩`. Use `choose a ha ea using hc`.

Set `A : Fin k → Af F` to `fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩`. Establish `e : y = ∑ j, fun i => A j ⊗ₜ[F] (s j : Fin n → E) i`. Use function extensionality and compare the values at `i`. Use `GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => (ea v i).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, map_sum]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, s j, (s j).2, rfl⟩`.
-/
theorem mem_latHat_iff {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ ∀ v, vecLoc v y ∈ latLoc F L v := by
  constructor
  · intro hy v
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact tmul_mem_latLoc (ha v) hx
    | zero =>
      have : vecLoc v (0 : Fin n → Af F ⊗[F] E) = 0 := funext fun i => map_zero _
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : vecLoc v (y + z) = vecLoc v y + vecLoc v z := funext fun i => map_add _ _ _
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : vecLoc v (-y) = -vecLoc v y := funext fun i => map_neg _ _
      rw [this]; exact neg_mem hy
  · intro h
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
    have hx : ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • (s j : Fin n → E) := fun w hw => by
      have : (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
      exact ⟨m, by simpa using (congrArg Subtype.val hm).symm⟩
    have hc : ∀ v, ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
        ∀ i, vecLoc v y i = ∑ j, a j ⊗ₜ[F] (s j : Fin n → E) i := fun v => by
      refine latLoc_induction (p := fun y => ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
        ∀ i, y i = ∑ j, a j ⊗ₜ[F] (s j : Fin n → E) i) ?_ ⟨0, fun _ => zero_mem _, fun i => by simp⟩ ?_ ?_ (h v)
      · intro a ha w hw
        obtain ⟨m, rfl⟩ := hx w hw
        refine ⟨fun j => m j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
        simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun j _ => (TensorProduct.smul_tmul _ _ _).symm
      · rintro y z ⟨a, ha, ea⟩ ⟨b, hb, eb⟩
        exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
          simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
      · rintro y ⟨a, ha, ea⟩
        exact ⟨-a, fun j => neg_mem (ha j), fun i => by
          simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩
    choose a ha ea using hc
    let A : Fin k → Af F := fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : y = ∑ j, fun i => A j ⊗ₜ[F] (s j : Fin n → E) i := by
      funext i
      refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => (ea v i).trans ?_
      rw [Finset.sum_apply, map_sum]
      rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, s j, (s j).2, rfl⟩

end Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

section Dual

omit [NumberField E]

def hLin (R : Type) [CommRing R] [Algebra F R] (y x : Fin n → R ⊗[F] E) : R ⊗[F] E := hR R σ J x y

omit [NumberField F] in
/- English proof (translation)
Simplify using `[hLin, hR, hform, mul_add, Finset.sum_add_distrib]`.
-/
theorem hLin_add_left (R : Type) [CommRing R] [Algebra F R] (y y' x : Fin n → R ⊗[F] E) :
    hLin σ J R (y + y') x = hLin σ J R y x + hLin σ J R y' x := by
  simp [hLin, hR, hform, mul_add, Finset.sum_add_distrib]

omit [NumberField F] in
/- English proof (translation)
Simplify using `only [hLin, hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hLin_smul_left (R : Type) [CommRing R] [Algebra F R] (c : R ⊗[F] E) (y x : Fin n → R ⊗[F] E) :
    hLin σ J R (c • y) x = c * hLin σ J R y x := by
  simp only [hLin, hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def dualLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) where
  carrier := {y | ∀ x ∈ latLoc F L v, hLin σ J (Fv F v) y x ∈ intLoc F E v}
  zero_mem' := fun x _ => by simp [hLin, hR, hform]
  add_mem' := fun hy hy' x hx => by rw [hLin_add_left]; exact add_mem (hy x hx) (hy' x hx)
  smul_mem' := fun c y hy x hx => by
    change hLin σ J _ (c.1 • y) x ∈ _
    rw [hLin_smul_left]; exact mul_mem c.2 (hy x hx)

def IsSelfDualAt (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  latLoc F L v = dualLoc σ J L v

/- English proof (translation)
Establish `e : ∀ y x : Fin n → Fv F v ⊗[F] E, hLin σ 1 (Fv F v) y x = ∑ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x i) * y i` using `fun y x => by`. Simplify using `[hLin, hR, hform, JR, Matrix.one_apply]`. Use extensionality with `y`. Rewrite using `[mem_latLoc_stdLattice]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy x hx`. Rewrite using `[e]`. Conclude with `sum_mem fun i _ => mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx i)) (hy i)`. Introduce `hy i`. Use `hy (Pi.single i 1) (mem_latLoc_stdLattice.2 fun j => by` as an intermediate fact.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h])`. Rewrite `this` using `[e, Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)]`.

Simplify using `using this`.
-/
theorem isSelfDualAt_stdLattice_one (v : HeightOneSpectrum (𝓞 F)) :
    IsSelfDualAt σ (1 : Matrix (Fin n) (Fin n) E) (stdLattice E n) v := by
  have e : ∀ y x : Fin n → Fv F v ⊗[F] E,
      hLin σ 1 (Fv F v) y x = ∑ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x i) * y i := fun y x => by
    simp [hLin, hR, hform, JR, Matrix.one_apply]
  ext y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy x hx
    rw [e]
    exact sum_mem fun i _ => mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx i)) (hy i)
  · intro hy i
    have := hy (Pi.single i 1) (mem_latLoc_stdLattice.2 fun j => by
      by_cases h : j = i
      · subst h; simp
      · simp [h])
    rw [e, Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)] at this
    simpa using this

end Dual

section Level

omit [NumberField E]

def stabLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GLoc σ J v) :=
  (stabGL (latLoc F L v)).comap (matHom _ σ J)

def levelOpen (L : Submodule (𝓞 E) (Fin n → E)) : Subgroup (GAd σ J) := ⨅ v, (stabLoc σ J L v).comap (proj σ J v)

def levelOff (L : Submodule (𝓞 E) (Fin n → E)) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GAd σ J) :=
  finAwayPts σ J S ⊓ ⨅ v, ⨅ (_ : v ∉ S), (stabLoc σ J L v).comap (proj σ J v)

def levelFin (L : Submodule (𝓞 E) (Fin n → E)) : Subgroup (GAd σ J) := levelOff σ J L ∅

def levelOffFin (L : Submodule (𝓞 E) (Fin n → E)) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GFin σ J) :=
  (levelOff σ J L S).comap (ofFin σ J)

def stabArch (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Subgroup (GArch σ J w) :=
  (UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) 1).comap ((MulAut.conj b⁻¹).toMonoidHom.comp (matHom _ σ J))

def levelAll (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) : Subgroup (GAd σ J) :=
  levelOpen σ J L ⊓ ⨅ w, (stabArch σ J w (bc (compInf F E w) a)).comap (projArch σ J w)

def IsLatticeFrame (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E),
    (∀ i, y i ∈ intLoc F E v) ↔ (bc (compFin F E v) a).1 *ᵥ y ∈ latLoc F L v

def IsMajorantFrame (a : GL (Fin n) (AF F ⊗[F] E)) : Prop :=
  ∀ w : InfinitePlace F, ∃ ε : Fin n → Bool,
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (bc (compInf F E w) a).1 * JR w.Completion J * (bc (compInf F E w) a).1 =
      Matrix.diagonal fun i => if ε i then 1 else -1

variable {σ J} {L : Submodule (𝓞 E) (Fin n → E)} {S : Finset (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stabLoc {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ ∀ y, y ∈ latLoc F L v ↔ (matHom _ σ J g).1 *ᵥ y ∈ latLoc F L v := Iff.rfl

/- English proof (translation)
Simplify using `[levelOpen, Subgroup.mem_iInf]`.
-/
theorem mem_levelOpen {g : GAd σ J} : g ∈ levelOpen σ J L ↔ ∀ v, proj σ J v g ∈ stabLoc σ J L v := by
  simp [levelOpen, Subgroup.mem_iInf]

/- English proof (translation)
Simplify using `[levelOff, Subgroup.mem_iInf, mem_finAwayPts, and_assoc]`.
-/
theorem mem_levelOff {g : GAd σ J} : g ∈ levelOff σ J L S ↔
    g ∈ finPts σ J ∧ (∀ v ∈ S, proj σ J v g = 1) ∧ ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v := by
  simp [levelOff, Subgroup.mem_iInf, mem_finAwayPts, and_assoc]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_levelOff, Subgroup.mem_inf, mem_finAwayPts, mem_levelOpen, and_assoc]`. Use `and_congr_right fun _ => and_congr_right fun h => ⟨fun h' v => ?_, fun h' v _ => h' v⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[h v hv]`.

Conclude with `one_mem _`. Conclude with `h' v hv`.
-/
theorem levelOff_eq : levelOff σ J L S = finAwayPts σ J S ⊓ levelOpen σ J L := by
  ext g
  rw [mem_levelOff, Subgroup.mem_inf, mem_finAwayPts, mem_levelOpen, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun h => ⟨fun h' v => ?_, fun h' v _ => h' v⟩
  by_cases hv : v ∈ S
  · rw [h v hv]; exact one_mem _
  · exact h' v hv

/- English proof (translation)
Simplify using `[levelFin, mem_levelOff]`.
-/
theorem mem_levelFin {g : GAd σ J} :
    g ∈ levelFin σ J L ↔ g ∈ finPts σ J ∧ ∀ v, proj σ J v g ∈ stabLoc σ J L v := by
  simp [levelFin, mem_levelOff]

/- English proof (translation)
Simplify using `[levelOffFin, mem_levelOff, mem_finPts]`.
-/
theorem mem_levelOffFin {g : GFin σ J} : g ∈ levelOffFin σ J L S ↔
    (∀ v ∈ S, projFinLoc σ J v g = 1) ∧ ∀ v ∉ S, projFinLoc σ J v g ∈ stabLoc σ J L v := by
  simp [levelOffFin, mem_levelOff, mem_finPts]

/- English proof (translation)
Simplify using `[stabArch]`.
-/
theorem mem_stabArch {w : InfinitePlace F} {b : GL (Fin n) (w.Completion ⊗[F] E)} {g : GArch σ J w} :
    g ∈ stabArch σ J w b ↔ b⁻¹ * matHom _ σ J g * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) 1 := by
  simp [stabArch]

/- English proof (translation)
Simplify using `[levelAll, mem_levelOpen, Subgroup.mem_iInf]`.
-/
theorem mem_levelAll {a : GL (Fin n) (AF F ⊗[F] E)} {g : GAd σ J} : g ∈ levelAll σ J L a ↔
    (∀ v, proj σ J v g ∈ stabLoc σ J L v) ∧ ∀ w, projArch σ J w g ∈ stabArch σ J w (bc (compInf F E w) a) := by
  simp [levelAll, mem_levelOpen, Subgroup.mem_iInf]

/- English proof (translation)
Use `mem_levelOff.2 ⟨mem_finPts.2 (by simp), fun u hu => proj_emb_ne σ J (fun e : u = v => hv (e ▸ hu)) k, fun u _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Simplify using `using hk`. Rewrite using `[proj_emb_ne σ J e]`.

Conclude with `one_mem _`.
-/
theorem emb_mem_levelOff {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {k : GLoc σ J v} (hk : k ∈ stabLoc σ J L v) :
    emb σ J v k ∈ levelOff σ J L S := by
  refine mem_levelOff.2 ⟨mem_finPts.2 (by simp), fun u hu => proj_emb_ne σ J (fun e : u = v => hv (e ▸ hu)) k,
    fun u _ => ?_⟩
  by_cases e : u = v
  · subst e; simpa using hk
  · rw [proj_emb_ne σ J e]; exact one_mem _

/- English proof (translation)
Introduce `v y` and use `by rw [map_one, Units.val_one, Matrix.one_mulVec, mem_latLoc_stdLattice]`.
-/
theorem isLatticeFrame_one : IsLatticeFrame (stdLattice E n) (1 : GL (Fin n) (AF F ⊗[F] E)) := fun v y => by
  rw [map_one, Units.val_one, Matrix.one_mulVec, mem_latLoc_stdLattice]

/- English proof (translation)
Introduce `w` and use `⟨fun _ => true, by simp [JR, cT_one]⟩`.
-/
theorem isMajorantFrame_one : IsMajorantFrame σ (1 : Matrix (Fin n) (Fin n) E) 1 := fun w =>
  ⟨fun _ => true, by simp [JR, cT_one]⟩

end Level

/- English proof (translation)
Rewrite using `[← projFinLoc_projFin]`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom _ y i`.
-/
theorem vecLoc_mulVec (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) (y : Fin n → Af F ⊗[F] E) :
    vecLoc v ((Formalism.MainNotions.StandardLattice.finMat σ J g).mulVec y) = (matHom _ σ J (proj σ J v g)).1 *ᵥ vecLoc v y := by
  rw [← projFinLoc_projFin]
  funext i
  exact RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom _ y i

/- English proof (translation)
Simplify using `only [mem_levelOpen, mem_latHat_iff hL, vecLoc_mulVec]`. Use `⟨fun h y => forall_congr' fun v => h v _, fun h v z => ?_⟩` and prove the remaining obligations. Set `y : Fin n → Af F ⊗[F] E` to `fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) (z i)`. Establish `h1 : vecLoc v y = z`. Use function extensionality and compare the values at `fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (evalV_singleFin_self v) _`.

Establish `h2 : ∀ u, u ≠ v → vecLoc u y = 0` using `fun u hu =>`. Use function extensionality and compare the values at `fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (evalV_singleFin_ne hu) _`. Rewrite using `[← h1]`. Use `⟨fun hz => (h y).1 (fun u => ?_) v, fun hz => (h y).2 (fun u => ?_) v⟩` and prove the remaining obligations. Distinguish the cases in `e : u = v`.

Substitute `e` using the available equality. Conclude with `hz`. Rewrite using `[h2 u e]`. Conclude with `zero_mem _`. Distinguish the cases in `e : u = v`.

Substitute `e` using the available equality. Conclude with `hz`. Rewrite using `[h2 u e, Matrix.mulVec_zero]`. Conclude with `zero_mem _`.
-/
theorem mem_levelOpen_iff_latHat {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (g : GAd σ J) :
    g ∈ levelOpen σ J L ↔ ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (Formalism.MainNotions.StandardLattice.finMat σ J g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  simp only [mem_levelOpen, mem_latHat_iff hL, vecLoc_mulVec]
  refine ⟨fun h y => forall_congr' fun v => h v _, fun h v z => ?_⟩
  let y : Fin n → Af F ⊗[F] E := fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) (z i)
  have h1 : vecLoc v y = z :=
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (evalV_singleFin_self v) _
  have h2 : ∀ u, u ≠ v → vecLoc u y = 0 := fun u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (evalV_singleFin_ne hu) _
  rw [← h1]
  refine ⟨fun hz => (h y).1 (fun u => ?_) v, fun hz => (h y).2 (fun u => ?_) v⟩
  · by_cases e : u = v
    · subst e; exact hz
    · rw [h2 u e]; exact zero_mem _
  · by_cases e : u = v
    · subst e; exact hz
    · rw [h2 u e, Matrix.mulVec_zero]; exact zero_mem _

section Height

def height (g : GAd σ J) : ℝ≥0 := heightGL F (matHom _ σ J g)

def heightIn (a : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : ℝ≥0 := heightGL F (a⁻¹ * matHom _ σ J g * a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem height_eq (g : GAd σ J) : height σ J g =
    (∏ w, htInf F w (matHom _ σ J (projArch σ J w g))) * ∏ᶠ v, htFin F v (matHom _ σ J (proj σ J v g)) := rfl

/- English proof (translation)
The claim follows from `one_le_heightGL F _`.
-/
theorem one_le_height (g : GAd σ J) : 1 ≤ height σ J g := one_le_heightGL F _
/- English proof (translation)
Simplify using `[height]`.
-/
@[simp] theorem height_one : height σ J 1 = 1 := by simp [height]
/- English proof (translation)
Rewrite using `[height, map_inv, heightGL_inv, height]`.
-/
theorem height_inv (g : GAd σ J) : height σ J g⁻¹ = height σ J g := by rw [height, map_inv, heightGL_inv, height]
/- English proof (translation)
Rewrite using `[height, map_mul]`. Conclude with `heightGL_mul_le F _ _`.
-/
theorem height_mul_le (g h : GAd σ J) : height σ J (g * h) ≤ height σ J g * height σ J h := by
  rw [height, map_mul]; exact heightGL_mul_le F _ _

/- English proof (translation)
The claim follows from `(Finset.single_le_prod' (f := fun w => htInf F w (matHom _ σ J (projArch σ J w g))) (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)).trans (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))`.
-/
theorem htInf_le_height (w : InfinitePlace F) (g : GAd σ J) :
    htInf F w (matHom _ σ J (projArch σ J w g)) ≤ height σ J g :=
  (Finset.single_le_prod' (f := fun w => htInf F w (matHom _ σ J (projArch σ J w g)))
    (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)).trans
    (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))

/- English proof (translation)
The claim follows from `htOf_eq_one.2 ⟨normFin_one_le F v, normFin_one_le F v⟩`.
-/
theorem htFin_one (v : HeightOneSpectrum (𝓞 F)) : htFin F v (1 : GL (Fin n) (Fv F v ⊗[F] E)) = 1 :=
  htOf_eq_one.2 ⟨normFin_one_le F v, normFin_one_le F v⟩

/- English proof (translation)
The claim follows from `htOf_eq_one.2 ⟨normInf_one_le F w, normInf_one_le F w⟩`.
-/
theorem htInf_one (w : InfinitePlace F) : htInf F w (1 : GL (Fin n) (w.Completion ⊗[F] E)) = 1 :=
  htOf_eq_one.2 ⟨normInf_one_le F w, normInf_one_le F w⟩

/- English proof (translation)
Rewrite using `[height_eq, finprod_eq_single _ v fun u hu => by rw [proj_emb_ne σ J hu, map_one, htFin_one], proj_emb_self]`. Simplify using `only [projArch_emb, map_one, htInf_one, Finset.prod_const_one, one_mul]`.
-/
theorem height_emb (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    height σ J (emb σ J v x) = htFin F v (matHom _ σ J x) := by
  rw [height_eq, finprod_eq_single _ v fun u hu => by rw [proj_emb_ne σ J hu, map_one, htFin_one], proj_emb_self]
  simp only [projArch_emb, map_one, htInf_one, Finset.prod_const_one, one_mul]

/- English proof (translation)
Rewrite using `[height_eq, Finset.prod_eq_single w (fun u _ hu => by rw [projArch_embArch_ne σ J hu, map_one, htInf_one]) (by simp), projArch_embArch_self]`. Simplify using `only [proj_embArch, map_one, htFin_one, finprod_one, mul_one]`.
-/
theorem height_embArch (w : InfinitePlace F) (x : GArch σ J w) :
    height σ J (embArch σ J w x) = htInf F w (matHom _ σ J x) := by
  rw [height_eq, Finset.prod_eq_single w (fun u _ hu => by rw [projArch_embArch_ne σ J hu, map_one, htInf_one])
    (by simp), projArch_embArch_self]
  simp only [proj_embArch, map_one, htFin_one, finprod_one, mul_one]

/- English proof (translation)
Rewrite using `[map_mul]`. Use `group`.
-/
theorem conj_mul (a : GL (Fin n) (AF F ⊗[F] E)) (g h : GAd σ J) :
    a⁻¹ * matHom _ σ J (g * h) * a = (a⁻¹ * matHom _ σ J g * a) * (a⁻¹ * matHom _ σ J h * a) := by
  rw [map_mul]; group

variable {σ} in
/- English proof (translation)
Use `(normInf_le_iff F w).2 fun τ => ?_` and prove the remaining obligations. Establish `h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) u.1 * 1 * u.1 = 1` using `hu`. Establish `h2 : star (u.1.map (infEmb τ)) * u.1.map (infEmb τ) = 1`. Establish `h3 : star (u.1.map (infEmb τ)) = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) u.1).map (infEmb τ)`. Use extensionality with `i j`.

Conclude with `infEmb_sigR h τ _`. Rewrite `h1` using `[mul_one]`. Rewrite using `[h3, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h4` using `opNorm_one_le (n := Fin n)`. Rewrite `h4` using `[← h2, opNorm, map_mul, map_star, CStarRing.nnnorm_star_mul_self]`.

Assume the negation of the conclusion as `hc`. Conclude with `absurd h4 (not_le.2 (one_lt_mul'' (not_le.1 hc) (not_le.1 hc)))`.
-/
theorem normInf_le_one_of_unitary (h : IsCMExt F E σ) {w : InfinitePlace F} {u : GL (Fin n) (w.Completion ⊗[F] E)}
    (hu : u ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) 1) : normInf F w u.1 ≤ 1 := by
  refine (normInf_le_iff F w).2 fun τ => ?_
  have h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) u.1 * 1 * u.1 = 1 := hu
  have h2 : star (u.1.map (infEmb τ)) * u.1.map (infEmb τ) = 1 := by
    have h3 : star (u.1.map (infEmb τ)) = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) u.1).map (infEmb τ) := by
      ext i j
      exact infEmb_sigR h τ _
    rw [mul_one] at h1
    rw [h3, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h4 := opNorm_one_le (n := Fin n)
  rw [← h2, opNorm, map_mul, map_star, CStarRing.nnnorm_star_mul_self] at h4
  by_contra hc
  exact absurd h4 (not_le.2 (one_lt_mul'' (not_le.1 hc) (not_le.1 hc)))

variable {σ J} in
/- English proof (translation)
Use `(normFin_le_iff F v).2 fun i j => absFin_le_one_of_mem_intLoc ?_` and prove the remaining obligations. Establish `h1` using `(mem_stabLoc.1 hk _).1 ((ha v (Pi.single j 1)).1 fun l => by`. Distinguish the cases in `e : l = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[e])`. Establish `h2` using `(ha v (((bc (compFin F E v) a)⁻¹ * matHom _ σ J k * bc (compFin F E v) a).1 *ᵥ Pi.single j 1)).2 (by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul, ← Matrix.mulVec_mulVec]) i` and apply the resulting hypothesis. Simplify using `using h2`.
-/
theorem normFin_conj_le_one {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    (ha : IsLatticeFrame L a) {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v} (hk : k ∈ stabLoc σ J L v) :
    normFin F v ((bc (compFin F E v) a)⁻¹ * matHom _ σ J k * bc (compFin F E v) a).1 ≤ 1 := by
  refine (normFin_le_iff F v).2 fun i j => absFin_le_one_of_mem_intLoc ?_
  have h1 := (mem_stabLoc.1 hk _).1 ((ha v (Pi.single j 1)).1 fun l => by
    by_cases e : l = j
    · subst e; simp
    · simp [e])
  have h2 := (ha v (((bc (compFin F E v) a)⁻¹ * matHom _ σ J k * bc (compFin F E v) a).1 *ᵥ Pi.single j 1)).2 (by
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec]) i
  simpa using h2

end Height

section Moderate

def IsModerate {G X : Type*} [Norm X] (ht : G → ℝ≥0) (f : G → X) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g, ‖f g‖ ≤ C * (ht g : ℝ) ^ N

/- English proof (translation)
Take `⟨C, N, h⟩` from `h`. Conclude with `⟨max C 0, N, le_max_right _ _, fun g => (h g).trans (by gcongr; exact le_max_left _ _)⟩`.
-/
theorem IsModerate.exists_nonneg {G X : Type*} [Norm X] {ht : G → ℝ≥0} {f : G → X} (h : IsModerate ht f) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * (ht g : ℝ) ^ N := by
  obtain ⟨C, N, h⟩ := h
  exact ⟨max C 0, N, le_max_right _ _, fun g => (h g).trans (by gcongr; exact le_max_left _ _)⟩

/- English proof (translation)
Take `⟨C, N, hC, h⟩` from `h.exists_nonneg`. Use `⟨C * c ^ N, m * N, fun g => (h (φ g)).trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, pow_mul, ← mul_pow]`. Use `gcongr`. Conclude with `hφ g` after adjusting the coercions.
-/
theorem IsModerate.comp {G G' X : Type*} [Norm X] {ht : G → ℝ≥0} {ht' : G' → ℝ≥0} {f : G → X} (h : IsModerate ht f)
    (φ : G' → G) {c : ℝ≥0} {m : ℕ} (hφ : ∀ g, ht (φ g) ≤ c * ht' g ^ m) : IsModerate ht' (f ∘ φ) := by
  obtain ⟨C, N, hC, h⟩ := h.exists_nonneg
  refine ⟨C * c ^ N, m * N, fun g => (h (φ g)).trans ?_⟩
  rw [mul_assoc, pow_mul, ← mul_pow]
  gcongr
  exact_mod_cast hφ g

/- English proof (translation)
Take `⟨C, N, hC, h⟩` from `h.exists_nonneg`. Take `⟨C', N', hC', h'⟩` from `h'.exists_nonneg`. Use `⟨C + C', max N N', fun g => (norm_add_le _ _).trans ?_⟩` and prove the remaining obligations. Establish `: (1 : ℝ) ≤ ht g` using `h1 g`. Rewrite using `[add_mul]`.

Apply the tactic sequence `refine add_le_add ((h g).trans ?_) ((h' g).trans ?_) <;> gcongr <;> simp`.
-/
theorem IsModerate.add {G X : Type*} [SeminormedAddGroup X] {ht : G → ℝ≥0} (h1 : ∀ g, 1 ≤ ht g) {f f' : G → X}
    (h : IsModerate ht f) (h' : IsModerate ht f') : IsModerate ht (f + f') := by
  obtain ⟨C, N, hC, h⟩ := h.exists_nonneg
  obtain ⟨C', N', hC', h'⟩ := h'.exists_nonneg
  refine ⟨C + C', max N N', fun g => (norm_add_le _ _).trans ?_⟩
  have : (1 : ℝ) ≤ ht g := h1 g
  rw [add_mul]
  refine add_le_add ((h g).trans ?_) ((h' g).trans ?_) <;> gcongr <;> simp

/- English proof (translation)
Take `⟨C, N, hC, h⟩` from `h.exists_nonneg`. Take `⟨C', N', h'⟩` from `h'`. Use `⟨C * C', N + N', fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply', norm_smul, pow_add, mul_mul_mul_comm]`. Conclude with `mul_le_mul (h g) (h' g) (norm_nonneg _) (by positivity)`.
-/
theorem IsModerate.smul {G R X : Type*} [SeminormedAddGroup R] [SeminormedAddGroup X] [SMul R X] [NormSMulClass R X]
    {ht : G → ℝ≥0} {f : G → R} {f' : G → X} (h : IsModerate ht f) (h' : IsModerate ht f') :
    IsModerate ht (f • f') := by
  obtain ⟨C, N, hC, h⟩ := h.exists_nonneg
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨C * C', N + N', fun g => ?_⟩
  rw [Pi.smul_apply', norm_smul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul (h g) (h' g) (norm_nonneg _) (by positivity)

def ModerateGrowth {X : Type*} [Norm X] (f : GAd σ J → X) : Prop := IsModerate (height σ J) f

def ModerateGrowth₂ {X : Type*} [Norm X] {n' : ℕ} (J' : Matrix (Fin n') (Fin n') E) (f : GAd σ J × GAd σ J' → X) :
    Prop := IsModerate (fun p => height σ J p.1 * height σ J' p.2) f

variable {σ J}

/- English proof (translation)
The claim follows from `IsModerate.comp h (· * x) (m := 1) (c := height σ J x) fun g => by simpa [mul_comm] using height_mul_le σ J g x`.
-/
theorem ModerateGrowth.mul_right {X : Type*} [Norm X] {f : GAd σ J → X} (h : ModerateGrowth σ J f) (x : GAd σ J) :
    ModerateGrowth σ J fun g => f (g * x) :=
  IsModerate.comp h (· * x) (m := 1) (c := height σ J x) fun g => by
    simpa [mul_comm] using height_mul_le σ J g x

/- English proof (translation)
The claim follows from `IsModerate.comp h (x * ·) (m := 1) (c := height σ J x) fun g => by simpa using height_mul_le σ J x g`.
-/
theorem ModerateGrowth.mul_left {X : Type*} [Norm X] {f : GAd σ J → X} (h : ModerateGrowth σ J f) (x : GAd σ J) :
    ModerateGrowth σ J fun g => f (x * g) :=
  IsModerate.comp h (x * ·) (m := 1) (c := height σ J x) fun g => by simpa using height_mul_le σ J x g

/- English proof (translation)
The claim follows from `IsModerate.add (one_le_height σ J) h h'`.
-/
theorem ModerateGrowth.add {X : Type*} [SeminormedAddGroup X] {f f' : GAd σ J → X} (h : ModerateGrowth σ J f)
    (h' : ModerateGrowth σ J f') : ModerateGrowth σ J (f + f') := IsModerate.add (one_le_height σ J) h h'

end Moderate

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

def frameLat {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : Submodule (𝓞 E) (Fin V.rank → E) :=
  V.L0.comap (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 E))

/- English proof (translation)
Simplify using `[frameLat, Module.Basis.equivFun_symm_apply]`.
-/
theorem mem_frameLat {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) (x : Fin V.rank → E) :
    x ∈ frameLat V ↔ ∑ i, x i • V.frame i ∈ V.L0 := by
  simp [frameLat, Module.Basis.equivFun_symm_apply]

/- English proof (translation)
Establish `: frameLat V = V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))` using `(Submodule.map_equiv_eq_comap_symm (V.frame.equivFun.restrictScalars (𝓞 E)) V.L0).symm`. Rewrite using `[this]`. Conclude with `V.standardTuple_isLattice.fg.map _`.
-/
theorem frameLat_fg {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : (frameLat V).FG := by
  have : frameLat V = V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) :=
    (Submodule.map_equiv_eq_comap_symm (V.frame.equivFun.restrictScalars (𝓞 E)) V.L0).symm
  rw [this]
  exact V.standardTuple_isLattice.fg.map _

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D)

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩`.
-/
theorem isCMExt_host (D : D7) : IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GQ_eq : GQ V = ratPts D.sp.cm.sig V.gram := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GfC_eq : GfC V = finPts D.sp.cm.sig V.gram := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem GinfC_eq : GinfC V = infPts D.sp.cm.sig V.gram := rfl
/- English proof (translation)
The claim follows from `Set.ext fun x => (mem_frameLat V x).symm`.
-/
theorem hermitianSpaceBaseLattice_eq_frameLattice : Formalism.MainNotions.StandardLattice.L0c D V = (frameLat V : Set _) := Set.ext fun x => (mem_frameLat V x).symm

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[levelOff_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_finAwayPts, mem_levelOpen_iff_latHat _ _ (frameLat_fg V), ← hermitianSpaceBaseLattice_eq_frameLattice, and_assoc]`. Use `and_congr_right fun _ => and_comm.trans (and_congr_left fun _ => forall₂_congr fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[← projFinLoc_projFin]`. Conclude with `⟨fun h => Subtype.ext (Units.ext h), fun h => congrArg (fun x => (matHom _ _ _ x).1) h⟩`.
-/
theorem KsphC_eq (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    KsphC V S = (levelOff D.sp.cm.sig V.gram (frameLat V) S : Set _) := by
  ext g
  rw [levelOff_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_finAwayPts, mem_levelOpen_iff_latHat _ _ (frameLat_fg V),
    ← hermitianSpaceBaseLattice_eq_frameLattice, and_assoc]
  refine and_congr_right fun _ => and_comm.trans (and_congr_left fun _ => forall₂_congr fun v _ => ?_)
  rw [← projFinLoc_projFin]
  exact ⟨fun h => Subtype.ext (Units.ext h), fun h => congrArg (fun x => (matHom _ _ _ x).1) h⟩

end Record

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩`.
-/
theorem isCMExt_of_isCMField (E : Type) [Field E] [NumberField E] [IsCMField E] :
    IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, fun g => by simp⟩`.
-/
example : ModerateGrowth σ J fun g => (height σ J g : ℝ) := ⟨1, 1, fun g => by simp⟩

/- English proof (translation)
Introduce `h`. Use `letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))`. Take `⟨a, ha⟩` from `NontriviallyNormedField.non_trivial (α := Fv F v)`. Establish `h1 : (fun _ => a ⊗ₜ[F] (1 : E)) ∈ dualLoc σ (0 : Matrix (Fin 1) (Fin 1) E) (stdLattice E 1) v` using `fun x _ => by simp [hLin, hR, hform, JR]`. Rewrite `h1` using `[← h, mem_latLoc_stdLattice]`.

Establish `h2` using `absFin_le_one_of_mem_intLoc (h1 0)`. Rewrite `h2` using `[absFin_tmul_one]`. Conclude with `absurd (show ‖a‖ ≤ 1 from h2) (not_le.2 ha)`.
-/
example (v : HeightOneSpectrum (𝓞 F)) : ¬ IsSelfDualAt σ (0 : Matrix (Fin 1) (Fin 1) E) (stdLattice E 1) v := by
  intro h
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨a, ha⟩ := NontriviallyNormedField.non_trivial (α := Fv F v)
  have h1 : (fun _ => a ⊗ₜ[F] (1 : E)) ∈ dualLoc σ (0 : Matrix (Fin 1) (Fin 1) E) (stdLattice E 1) v :=
    fun x _ => by simp [hLin, hR, hform, JR]
  rw [← h, mem_latLoc_stdLattice] at h1
  have h2 := absFin_le_one_of_mem_intLoc (h1 0)
  rw [absFin_tmul_one] at h2
  exact absurd (show ‖a‖ ≤ 1 from h2) (not_le.2 ha)

/- English proof (translation)
Simplify using `[normFin, absFin_tmul_one, Finset.sup_const]`.
-/
example (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    normFin F v (Matrix.of fun _ _ : Fin 1 => a ⊗ₜ[F] (1 : E)) = ‖a‖₊ := by
  simp [normFin, absFin_tmul_one, Finset.sup_const]

end GlobalTheory.AdelicU

end
