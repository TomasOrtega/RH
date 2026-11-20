import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.SplTApply

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

namespace Memb

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') {n : ℕ}

def mapV : (Fin n → R ⊗[F] E) →+ (Fin n → R' ⊗[F] E) :=
  (tensMap (E := E) φ).toAddMonoidHom.compLeft (Fin n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mapV_apply (x : Fin n → R ⊗[F] E) (i : Fin n) :
    mapV (E := E) φ x i = tensMap (E := E) φ (x i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[map_mul]`.
-/
theorem mapV_smul (c : R ⊗[F] E) (x : Fin n → R ⊗[F] E) :
    mapV (E := E) φ (c • x) = tensMap (E := E) φ c • mapV (E := E) φ x := by
  funext i
  simp [map_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, tensMap_inclR]`.
-/
theorem mapV_ratV (v : Fin n → E) : mapV (E := E) φ (ratV (F := F) R v) = ratV (F := F) R' v := by
  funext i
  simp [ratV, tensMap_inclR]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `Matrix.mulVec (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (tensMap (E := E) φ)) (fun j => tensMap (E := E) φ (x j)) i = tensMap (E := E) φ (Matrix.mulVec ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) x i)`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem lin_haMap (g : HA R σ J) (x : Fin n → R ⊗[F] E) :
    lin R' σ J (haMap σ J φ g) (mapV (E := E) φ x) = mapV (E := E) φ (lin R σ J g x) := by
  funext i
  change Matrix.mulVec (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
      (tensMap (E := E) φ)) (fun j => tensMap (E := E) φ (x j)) i =
    tensMap (E := E) φ (Matrix.mulVec ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)) x i)
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Rewrite using `[mapV_ratV]`. Conclude with `Submodule.subset_span ⟨a, ha, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [mapV_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem mapV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → R ⊗[F] E)
    (hx : x ∈ spanR (F := F) R Y s) : mapV (E := E) φ x ∈ spanR (F := F) R' Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [mapV_ratV]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mapV_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, map_sum, map_mul, mapV_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : tensMap (E` using `E) φ (sigR R σ (x i)) = sigR R' σ (tensMap (E := E) φ (x i)) := by`. Use `congrArg (fun f : R ⊗[F] E →+* R' ⊗[F] E => f (x i)) (tensMap_sigR (E := E) φ σ)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h1]`. Simplify using `[JR, tensMap_inclR]`.
-/
theorem hR_mapV (x y : Fin n → R ⊗[F] E) :
    hR R' σ J (mapV (E := E) φ x) (mapV (E := E) φ y) = tensMap (E := E) φ (hR R σ J x y) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, mapV_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : tensMap (E := E) φ (sigR R σ (x i)) = sigR R' σ (tensMap (E := E) φ (x i)) := by
    have := congrArg (fun f : R ⊗[F] E →+* R' ⊗[F] E => f (x i)) (tensMap_sigR (E := E) φ σ)
    simpa using this
  rw [h1]
  simp [JR, tensMap_inclR]

/- English proof (translation)
Simplify using `[hR, Formalism.UG.hform]`.
-/
theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

end Gen

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨h1, h2⟩`. Use function extensionality and compare the values at `i`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[splT_apply, splT_apply]`. Conclude with `Prod.ext (congrFun h1 i) (congrFun h2 i)`.
-/
theorem eq_iff_split (hinj : Function.Injective (splT (F := F) (E := E)))
    (w u : Fin n → AF F ⊗[F] E) :
    w = u ↔ mapV (E := E) (fstA F) w = mapV (E := E) (fstA F) u ∧
      mapV (E := E) (sndA F) w = mapV (E := E) (sndA F) u := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    apply hinj
    rw [splT_apply, splT_apply]
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

/- English proof (translation)
Use `choose v hv using fun i => hsurj (y₁ i, y₂ i)`. Use `⟨v, funext fun i => ?_, funext fun i => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Prod.fst (hv i)`. Conclude with `congrArg Prod.snd (hv i)`.
-/
theorem exists_split (hsurj : Function.Surjective (splT (F := F) (E := E)))
    (y₁ : Fin n → Ainf F ⊗[F] E) (y₂ : Fin n → Af F ⊗[F] E) :
    ∃ v : Fin n → AF F ⊗[F] E, mapV (E := E) (fstA F) v = y₁ ∧ mapV (E := E) (sndA F) v = y₂ := by
  choose v hv using fun i => hsurj (y₁ i, y₂ i)
  refine ⟨v, funext fun i => ?_, funext fun i => ?_⟩
  · exact congrArg Prod.fst (hv i)
  · exact congrArg Prod.snd (hv i)

/- English proof (translation)
Simplify using `only [spanR, Set.image_eq_range] at h1 h2 ⊢`. Rewrite `h1`, `h2` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c1, hc1⟩` from `h1`. Take `⟨c2, hc2⟩` from `h2`. Use `choose c hc using fun a => hbij.2 (c1 a, c2 a)`.

Establish `hw : w = ∑ a, c a • ratV (F` using `F) (AF F) (Y a) := by`. Rewrite using `[eq_iff_split hbij.1]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hc1, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[mapV_smul, mapV_ratV]`. Use `congr 1`. Conclude with `(congrArg Prod.fst (hc a)).symm`. Rewrite using `[← hc2, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[mapV_smul, mapV_ratV]`. Use `congr 1`. Conclude with `(congrArg Prod.snd (hc a)).symm`. Rewrite using `[hw, Submodule.mem_span_range_iff_exists_fun]`. Conclude with `⟨c, rfl⟩`.
-/
theorem mem_spanR_of_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E)
    (h1 : mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s)
    (h2 : mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s) :
    w ∈ spanR (F := F) (AF F) Y s := by
  classical
  simp only [spanR, Set.image_eq_range] at h1 h2 ⊢
  rw [Submodule.mem_span_range_iff_exists_fun] at h1 h2
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  choose c hc using fun a => hbij.2 (c1 a, c2 a)
  have hw : w = ∑ a, c a • ratV (F := F) (AF F) (Y a) := by
    rw [eq_iff_split hbij.1]
    constructor
    · rw [← hc1, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.fst (hc a)).symm
    · rw [← hc2, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.snd (hc a)).symm
  rw [hw, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨c, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨mapV_mem_spanR _ Y s w h, mapV_mem_spanR _ Y s w h⟩, fun h => mem_spanR_of_split hbij Y s w h.1 h.2⟩`.
-/
theorem mem_spanR_iff_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E) :
    w ∈ spanR (F := F) (AF F) Y s ↔ mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s ∧
      mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s :=
  ⟨fun h => ⟨mapV_mem_spanR _ Y s w h, mapV_mem_spanR _ Y s w h⟩,
    fun h => mem_spanR_of_split hbij Y s w h.1 h.2⟩

end Split

end Memb

open Memb

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Introduce `g g' h`. Establish `h1 : haMap σ J (fstA F) g = haMap σ J (fstA F) g'` using `congrArg Prod.fst h`. Establish `h2 : haMap σ J (sndA F) g = haMap σ J (sndA F) g'` using `congrArg Prod.snd h`. Establish `hm : HA.mat (AF F) σ J g = HA.mat (AF F) σ J g'`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[splT_apply, splT_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `congrArg (fun k => ((HA.mat (Ainf F) σ J k : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) h1`. Conclude with `congrArg (fun k => ((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) h2`.

Conclude with `Subtype.ext hm`.
-/
theorem splitA_injective (hinj : Function.Injective (splT (F := F) (E := E))) :
    Function.Injective (splitA σ J) := by
  intro g g' h
  have h1 : haMap σ J (fstA F) g = haMap σ J (fstA F) g' := congrArg Prod.fst h
  have h2 : haMap σ J (sndA F) g = haMap σ J (sndA F) g' := congrArg Prod.snd h
  have hm : HA.mat (AF F) σ J g = HA.mat (AF F) σ J g' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    apply hinj
    rw [splT_apply, splT_apply]
    refine Prod.ext ?_ ?_
    · exact congrArg (fun k => ((HA.mat (Ainf F) σ J k : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) h1
    · exact congrArg (fun k => ((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) h2
  exact Subtype.ext hm

/- English proof (translation)
Unfold `Hsub`. Rewrite using `[mem_stabT, mem_stabT, mem_stabT]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun b => ?_, fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[← mapV_ratV (fstA F), lin_haMap, h b]`. Rewrite using `[← mapV_ratV (sndA F), lin_haMap, h b]`. Introduce and unpack `⟨h1, h2⟩ b`. Rewrite using `[eq_iff_split hinj]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← lin_haMap, mapV_ratV]`. Conclude with `h1 b`. Rewrite using `[← lin_haMap, mapV_ratV]`. Conclude with `h2 b`.
-/
theorem mem_Hsub_iff (hinj : Function.Injective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Hsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Hsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Hsub (Af F) σ J P := by
  unfold Hsub
  rw [mem_stabT, mem_stabT, mem_stabT]
  constructor
  · intro h
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [← mapV_ratV (fstA F), lin_haMap, h b]
    · rw [← mapV_ratV (sndA F), lin_haMap, h b]
  · rintro ⟨h1, h2⟩ b
    rw [eq_iff_split hinj]
    constructor
    · rw [← lin_haMap, mapV_ratV]
      exact h1 b
    · rw [← lin_haMap, mapV_ratV]
      exact h2 b

/- English proof (translation)
Establish `hdiff : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E), mapV (E` using `E) φ (lin (AF F) σ J g v - v) = lin R' σ J (haMap σ J φ g) (mapV (E := E) φ v) - mapV (E := E) φ v := by`. Introduce `R' _ _ φ v`. Rewrite using `[map_sub, lin_haMap]`. Establish `hperp : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E), InXperp (AF F) σ J P v → InXperp R' σ J P (mapV (E` using `E) φ v) := by`. Introduce `R' _ _ φ v hv a`.

Rewrite using `[← mapV_ratV φ, hR_mapV, hv a, map_zero]`. Express the relevant statement in the definitionally equal form `(UniC (AF F) σ J P.e g ∧ ∀ v, InXperp (AF F) σ J P v → lin (AF F) σ J g v - v ∈ spanR (F := F) (AF F) P.e Set.univ) ↔ (UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧ ∀ v, InXperp (Ainf F) σ J P v → lin (Ainf F) σ J (haMap σ J (fstA F) g) v - v ∈ spanR (F := F) (Ainf F) P.e Set.un …`. Establish `huni : UniC (AF F) σ J P.e g ↔ UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧ UniC (Af F) σ J P.e (haMap σ J (sndA F) g)`. Unfold `UniC`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun b => ?_, fun b => ?_⟩` and prove the remaining obligations. Use `mapV_mem_spanR (E := E) (fstA F) P.e _ _ (h b)` as an intermediate fact. Rewrite `this` using `[hdiff, mapV_ratV]`. Then use the resulting hypothesis. Use `mapV_mem_spanR (E := E) (sndA F) P.e _ _ (h b)` as an intermediate fact.

Rewrite `this` using `[hdiff, mapV_ratV]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩ b`. Rewrite using `[mem_spanR_iff_split hbij, hdiff, hdiff, mapV_ratV, mapV_ratV]`. Conclude with `⟨h1 b, h2 b⟩`. Rewrite using `[huni]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hu1, hu2⟩, hX⟩`. Use `⟨⟨hu1, fun v₁ hv₁ => ?_⟩, ⟨hu2, fun v₂ hv₂ => ?_⟩⟩` and prove the remaining obligations. Take `⟨v, hv1, hv2⟩` from `exists_split hbij.2 v₁ 0`. Establish `hv : InXperp (AF F) σ J P v`.

Introduce `a`. Apply `hbij.1` to reduce the goal to its premises. Rewrite using `[map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2, hR_zero_right, hv₁ a]`. Both sides reduce to the same expression. Use `mapV_mem_spanR (E := E) (fstA F) P.e _ _ (hX v hv)` as an intermediate fact.

Rewrite `this` using `[hdiff, hv1]`. Then use the resulting hypothesis. Take `⟨v, hv1, hv2⟩` from `exists_split hbij.2 0 v₂`. Establish `hv : InXperp (AF F) σ J P v`. Introduce `a`. Apply `hbij.1` to reduce the goal to its premises.

Rewrite using `[map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2, hR_zero_right, hv₂ a]`. Both sides reduce to the same expression. Use `mapV_mem_spanR (E := E) (sndA F) P.e _ _ (hX v hv)` as an intermediate fact. Rewrite `this` using `[hdiff, hv2]`. Then use the resulting hypothesis. Introduce and unpack `⟨⟨hu1, hX1⟩, ⟨hu2, hX2⟩⟩`.

Use `⟨⟨hu1, hu2⟩, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_spanR_iff_split hbij, hdiff, hdiff]`. Conclude with `⟨hX1 _ (hperp _ v hv), hX2 _ (hperp _ v hv)⟩`.
-/
theorem mem_Nsub_iff (hbij : Function.Bijective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Nsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Nsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Nsub (Af F) σ J P := by
  have hdiff : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      mapV (E := E) φ (lin (AF F) σ J g v - v) =
        lin R' σ J (haMap σ J φ g) (mapV (E := E) φ v) - mapV (E := E) φ v := by
    intro R' _ _ φ v
    rw [map_sub, lin_haMap]
  have hperp : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      InXperp (AF F) σ J P v → InXperp R' σ J P (mapV (E := E) φ v) := by
    intro R' _ _ φ v hv a
    rw [← mapV_ratV φ, hR_mapV, hv a, map_zero]
  change (UniC (AF F) σ J P.e g ∧ ∀ v, InXperp (AF F) σ J P v →
      lin (AF F) σ J g v - v ∈ spanR (F := F) (AF F) P.e Set.univ) ↔
    (UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧ ∀ v, InXperp (Ainf F) σ J P v →
      lin (Ainf F) σ J (haMap σ J (fstA F) g) v - v ∈ spanR (F := F) (Ainf F) P.e Set.univ) ∧
    (UniC (Af F) σ J P.e (haMap σ J (sndA F) g) ∧ ∀ v, InXperp (Af F) σ J P v →
      lin (Af F) σ J (haMap σ J (sndA F) g) v - v ∈ spanR (F := F) (Af F) P.e Set.univ)
  have huni : UniC (AF F) σ J P.e g ↔ UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧
      UniC (Af F) σ J P.e (haMap σ J (sndA F) g) := by
    unfold UniC
    constructor
    · intro h
      refine ⟨fun b => ?_, fun b => ?_⟩
      · have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
      · have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
    · rintro ⟨h1, h2⟩ b
      rw [mem_spanR_iff_split hbij, hdiff, hdiff, mapV_ratV, mapV_ratV]
      exact ⟨h1 b, h2 b⟩
  rw [huni]
  constructor
  · rintro ⟨⟨hu1, hu2⟩, hX⟩
    refine ⟨⟨hu1, fun v₁ hv₁ => ?_⟩, ⟨hu2, fun v₂ hv₂ => ?_⟩⟩
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 v₁ 0
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₁ a]
        rfl
      have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv1] at this
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 0 v₂
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₂ a]
        rfl
      have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv2] at this
  · rintro ⟨⟨hu1, hX1⟩, ⟨hu2, hX2⟩⟩
    refine ⟨⟨hu1, hu2⟩, fun v hv => ?_⟩
    rw [mem_spanR_iff_split hbij, hdiff, hdiff]
    exact ⟨hX1 _ (hperp _ v hv), hX2 _ (hperp _ v hv)⟩

end PI.UnitaryGroupMassFormula.MeasWCore
