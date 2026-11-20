import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Plucker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]

abbrev Sub (ι m : Type) [Fintype m] : Type := ↥(Set.powersetCard ι (Fintype.card m))

def enE (S : Sub ι m) : m ≃ ↥S.1 :=
  Fintype.equivOfCardEq ((Fintype.card_coe S.1).trans S.2).symm

def en (S : Sub ι m) : m → ι := fun i => (enE S i : ι)

/- English proof (translation)
The claim follows from `(enE S i).2`.
-/
theorem en_mem (S : Sub ι m) (i : m) : en S i ∈ S.1 := (enE S i).2

/- English proof (translation)
Introduce `_ _ h` and use `(enE S).injective (Subtype.ext h)`.
-/
theorem en_injective (S : Sub ι m) : Function.Injective (en S) := fun _ _ h =>
  (enE S).injective (Subtype.ext h)

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `en_mem S i`. Introduce `hx`.

Conclude with `⟨(enE S).symm ⟨x, hx⟩, by simp [en]⟩`.
-/
theorem range_en (S : Sub ι m) : Set.range (en S) = (S.1 : Set ι) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact en_mem S i
  · intro hx
    exact ⟨(enE S).symm ⟨x, hx⟩, by simp [en]⟩

def cmp (M : Matrix ι ι R) : Matrix (Sub ι m) (Sub ι m) R :=
  Matrix.of fun t u => (M.submatrix (en t) (en u)).det

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cmp_apply (M : Matrix ι ι R) (t u : Sub ι m) : cmp M t u = (M.submatrix (en t) (en u)).det := rfl

/- English proof (translation)
Use extensionality with `t u`. Rewrite using `[cmp_apply, submatrix_mul M N (en t) id (en u) Function.bijective_id, GlobalTheory.det_mul_eq_sum_minors_of_enum en range_en, Matrix.mul_apply]`. Both sides reduce to the same expression.
-/
theorem cmp_mul (M N : Matrix ι ι R) : (cmp (M * N) : Matrix (Sub ι m) (Sub ι m) R) = cmp M * cmp N := by
  ext t u
  rw [cmp_apply, submatrix_mul M N (en t) id (en u) Function.bijective_id,
    GlobalTheory.det_mul_eq_sum_minors_of_enum en range_en, Matrix.mul_apply]
  rfl

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `(Set.powersetCard.exists_mem_notMem_iff_ne t t₀).1 h`. Establish `h1 : x ∈ Set.range (en t)` using `by rw [range_en]; exact hx`. Take `⟨i, rfl⟩` from `h1`. Conclude with `det_eq_zero_of_row_eq_zero i fun j => hM _ hx' _ (en_mem t₀ j)`.
-/
theorem cmp_eq_zero_of_block (M : Matrix ι ι R) {t t₀ : Sub ι m} (h : t ≠ t₀)
    (hM : ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), M r c = 0) : cmp M t t₀ = 0 := by
  obtain ⟨x, hx, hx'⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t t₀).1 h
  have h1 : x ∈ Set.range (en t) := by rw [range_en]; exact hx
  obtain ⟨i, rfl⟩ := h1
  exact det_eq_zero_of_row_eq_zero i fun j => hM _ hx' _ (en_mem t₀ j)

/- English proof (translation)
Use extensionality with `t u`. Break down `eq_or_ne t u with rfl | h` into its components or cases. Rewrite using `[one_apply_eq, cmp_apply, submatrix_one _ (en_injective t), det_one]`. Rewrite using `[one_apply_ne h]`. Use `cmp_eq_zero_of_block _ h fun r hr c hc => one_apply_ne fun e => hr (e ▸ hc)` and prove the remaining obligations.
-/
theorem cmp_one : (cmp (1 : Matrix ι ι R) : Matrix (Sub ι m) (Sub ι m) R) = 1 := by
  ext t u
  rcases eq_or_ne t u with rfl | h
  · rw [one_apply_eq, cmp_apply, submatrix_one _ (en_injective t), det_one]
  · rw [one_apply_ne h]
    refine cmp_eq_zero_of_block _ h fun r hr c hc => one_apply_ne fun e => hr (e ▸ hc)

/- English proof (translation)
Use extensionality with `t u`. Rewrite using `[map_apply, cmp_apply, cmp_apply, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem cmp_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix ι ι R) :
    (cmp (M.map f) : Matrix (Sub ι m) (Sub ι m) S) = (cmp M).map f := by
  ext t u
  rw [map_apply, cmp_apply, cmp_apply, RingHom.map_det]
  rfl

/- English proof (translation)
Use extensionality with `t u`. Simplify using `only [cmp_apply, conjTranspose_apply, ← det_conjTranspose, conjTranspose_submatrix]`.
-/
theorem cmp_conjTranspose (M : Matrix ι ι ℂ) :
    (cmp Mᴴ : Matrix (Sub ι m) (Sub ι m) ℂ) = (cmp M)ᴴ := by
  ext t u
  simp only [cmp_apply, conjTranspose_apply, ← det_conjTranspose, conjTranspose_submatrix]

/- English proof (translation)
Rewrite using `[cmp_apply, det_apply']`. Conclude with `O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)`.
-/
theorem cmp_mem (O : Subring R) (M : Matrix ι ι R) (h : ∀ r c, M r c ∈ O) (t u : Sub ι m) : cmp M t u ∈ O := by
  rw [cmp_apply, det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

/- English proof (translation)
Substitute `hs` using the available equality. Set `φ : m ≃ ((t₀.1 : Set ι) : Set ι)` to `Equiv.ofBijective (fun i => ⟨en t₀ i, en_mem t₀ i⟩) ⟨fun a b h => en_injective t₀ (congrArg Subtype.val h), fun x => by`. Establish `h1 : x.1 ∈ Set.range (en t₀)` using `by rw [range_en]; exact x.2`. Take `⟨i, hi⟩` from `h1`. Conclude with `⟨i, Subtype.ext hi⟩⟩`.

Rewrite using `[← det_submatrix_equiv_self φ]`. Both sides reduce to the same expression.
-/
theorem det_block (t₀ : Sub ι m) (s : Set ι) (hs : s = (t₀.1 : Set ι)) [Fintype s] [DecidableEq s]
    (M : Matrix ι ι R) : (M.submatrix (Subtype.val : s → ι) Subtype.val).det = cmp M t₀ t₀ := by
  subst hs
  let φ : m ≃ ((t₀.1 : Set ι) : Set ι) :=
    Equiv.ofBijective (fun i => ⟨en t₀ i, en_mem t₀ i⟩)
      ⟨fun a b h => en_injective t₀ (congrArg Subtype.val h), fun x => by
        have h1 : x.1 ∈ Set.range (en t₀) := by rw [range_en]; exact x.2
        obtain ⟨i, hi⟩ := h1
        exact ⟨i, Subtype.ext hi⟩⟩
  rw [← det_submatrix_equiv_self φ]
  rfl

/- English proof (translation)
Establish `h1 : ∀ a, ∃ c, en t c = f a` using `fun a => by`. Establish `: f a ∈ Set.range (en t)` using `by rw [range_en]; exact hr a`. Conclude with `this`. Use `choose s hs using h1`. Establish `hinj : Function.Injective s` using `fun a b h => hf (by rw [← hs a, ← hs b, h])`.

Set `σ : Equiv.Perm m` to `Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj)`. Establish `hM : M.submatrix f (en u) = (M.submatrix (en t) (en u)).submatrix σ id`. Use extensionality with `a c`. Simplify using `[σ, hs]`. Rewrite using `[hM, det_permute, ← cmp_apply, h0, mul_zero]`.
-/
theorem det_submatrix_eq_zero (M : Matrix ι ι R) (t u : Sub ι m) (f : m → ι) (hf : Function.Injective f)
    (hr : ∀ a, f a ∈ t.1) (h0 : cmp M t u = 0) : (M.submatrix f (en u)).det = 0 := by
  have h1 : ∀ a, ∃ c, en t c = f a := fun a => by
    have : f a ∈ Set.range (en t) := by rw [range_en]; exact hr a
    exact this
  choose s hs using h1
  have hinj : Function.Injective s := fun a b h => hf (by rw [← hs a, ← hs b, h])
  let σ : Equiv.Perm m := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj)
  have hM : M.submatrix f (en u) = (M.submatrix (en t) (en u)).submatrix σ id := by
    ext a c
    simp [σ, hs]
  rw [hM, det_permute, ← cmp_apply, h0, mul_zero]

/- English proof (translation)
Introduce `r hr c hc`. Use `set B : Matrix m m E := M.submatrix (en t₀) (en t₀) with hBdef`. Establish `hB : B.det ≠ 0`. Introduce `h0`. Establish `hz : (cmp M : Matrix (Sub ι m) (Sub ι m) E).det = 0`.

Use `det_eq_zero_of_column_eq_zero t₀ fun t => ?_` and prove the remaining obligations. Break down `eq_or_ne t t₀ with rfl | ht` into its components or cases. Conclude with `h0`. Conclude with `h t ht`. Rewrite `hu` using `[hz]`.

Conclude with `not_isUnit_zero hu`. Set `v : m → E` to `fun i => M r (en t₀ i)`. Establish `hr' : ∀ a, en t₀ a ≠ r` using `fun a e => hr (e ▸ en_mem t₀ a)`. Establish `hcr : ∀ i, Bᵀ.cramer v i = 0`. Introduce `i`.

Rewrite using `[cramer_apply]`. Set `f : m → ι` to `Function.update (en t₀) i r`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Apply the tactic sequence `by_cases ha : a = i <;> by_cases hb : b = i`.

Rewrite using `[ha, hb]`. Substitute `ha` using the available equality. Simplify using `only [f, Function.update_self, Function.update_of_ne hb] at hab`. Conclude with `absurd hab.symm (hr' b)`. Substitute `hb` using the available equality.

Simplify using `only [f, Function.update_self, Function.update_of_ne ha] at hab`. Conclude with `absurd hab (hr' a)`. Simplify using `only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab`. Conclude with `en_injective t₀ hab`. Set `T : Finset ι` to `Finset.univ.map ⟨f, hf⟩`.

Establish `hT : T.card = Fintype.card m` using `by simp [T]`. Set `t : Sub ι m` to `⟨T, hT⟩`. Establish `hft : ∀ a, f a ∈ t.1` using `fun a => Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩`. Establish `hne : t ≠ t₀`. Introduce `e`.

Establish `h2 : r ∈ t.1`. Use `hft i` as an intermediate fact. Simplify `this` using `[f]`. Rewrite `h2` using `[e]`. Conclude with `hr h2`.

Establish `h3` using `det_submatrix_eq_zero M t t₀ f hf hft (h t hne)`. Establish `h4 : Bᵀ.updateCol i v = (M.submatrix f (en t₀))ᵀ`. Use extensionality with `a b`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality.

Simplify using `[updateCol_apply, v, f]`. Simplify using `[updateCol_apply, hb, f, Function.update_of_ne hb, hBdef]`. Rewrite using `[h4, det_transpose, h3]`. Establish `hv : v = 0`. Establish `h5` using `mulVec_cramer Bᵀ v`.

Establish `h6 : Bᵀ.cramer v = 0` using `funext hcr`. Rewrite `h5` using `[h6, mulVec_zero, det_transpose]`. Conclude with `(smul_eq_zero.1 h5.symm).resolve_left hB`. Establish `h7 : c ∈ Set.range (en t₀)` using `by rw [range_en]; exact hc`. Take `⟨j, rfl⟩` from `h7`.

Conclude with `congrFun hv j`.
-/
theorem block_of_cmp {E : Type} [Field E] (M : Matrix ι ι E) (t₀ : Sub ι m)
    (hu : IsUnit (cmp M : Matrix (Sub ι m) (Sub ι m) E).det) (h : ∀ t, t ≠ t₀ → cmp M t t₀ = 0) :
    ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), M r c = 0 := by
  intro r hr c hc
  set B : Matrix m m E := M.submatrix (en t₀) (en t₀) with hBdef
  have hB : B.det ≠ 0 := by
    intro h0
    have hz : (cmp M : Matrix (Sub ι m) (Sub ι m) E).det = 0 := by
      refine det_eq_zero_of_column_eq_zero t₀ fun t => ?_
      rcases eq_or_ne t t₀ with rfl | ht
      · exact h0
      · exact h t ht
    rw [hz] at hu
    exact not_isUnit_zero hu
  let v : m → E := fun i => M r (en t₀ i)
  have hr' : ∀ a, en t₀ a ≠ r := fun a e => hr (e ▸ en_mem t₀ a)
  have hcr : ∀ i, Bᵀ.cramer v i = 0 := by
    intro i
    rw [cramer_apply]
    let f : m → ι := Function.update (en t₀) i r
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : a = i <;> by_cases hb : b = i
      · rw [ha, hb]
      · subst ha
        simp only [f, Function.update_self, Function.update_of_ne hb] at hab
        exact absurd hab.symm (hr' b)
      · subst hb
        simp only [f, Function.update_self, Function.update_of_ne ha] at hab
        exact absurd hab (hr' a)
      · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact en_injective t₀ hab
    let T : Finset ι := Finset.univ.map ⟨f, hf⟩
    have hT : T.card = Fintype.card m := by simp [T]
    let t : Sub ι m := ⟨T, hT⟩
    have hft : ∀ a, f a ∈ t.1 := fun a => Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩
    have hne : t ≠ t₀ := by
      intro e
      have h2 : r ∈ t.1 := by
        have := hft i
        simpa [f] using this
      rw [e] at h2
      exact hr h2
    have h3 := det_submatrix_eq_zero M t t₀ f hf hft (h t hne)
    have h4 : Bᵀ.updateCol i v = (M.submatrix f (en t₀))ᵀ := by
      ext a b
      by_cases hb : b = i
      · subst hb
        simp [updateCol_apply, v, f]
      · simp [updateCol_apply, hb, f, Function.update_of_ne hb, hBdef]
    rw [h4, det_transpose, h3]
  have hv : v = 0 := by
    have h5 := mulVec_cramer Bᵀ v
    have h6 : Bᵀ.cramer v = 0 := funext hcr
    rw [h6, mulVec_zero, det_transpose] at h5
    exact (smul_eq_zero.1 h5.symm).resolve_left hB
  have h7 : c ∈ Set.range (en t₀) := by rw [range_en]; exact hc
  obtain ⟨j, rfl⟩ := h7
  exact congrFun hv j

def cmpHom (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (R : Type) [CommRing R] :
    Matrix ι ι R →* Matrix (Sub ι m) (Sub ι m) R where
  toFun := cmp
  map_one' := cmp_one
  map_mul' := cmp_mul

def cGL (m : Type) [Fintype m] [DecidableEq m] : GL ι R →* GL (Sub ι m) R := Units.map (cmpHom ι m R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cGL_coe (g : GL ι R) : ((cGL m g : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp (g : Matrix ι ι R) := rfl

end GlobalTheory.CompanionTheory.Plucker

namespace GlobalTheory.CompanionTheory.Plucker

open PositivityTheory.RgEis

section Grp

variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

/- English proof (translation)
Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem cGL_inv_coe (g : GL ι R) :
    (((cGL m g)⁻¹ : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
  rw [← map_inv]
  rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stab {s : Set ι} {g : GL ι R} : g ∈ stab R s ↔
    ∀ r ∉ s, ∀ c ∈ s, (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0 := Iff.rfl

/- English proof (translation)
Rewrite `hp`, the goal using `[mem_stab]`. Introduce `r hr c hc`. Establish `hc' : c = t₀` using `hc`. Substitute `hc'` using the available equality. Establish `hr' : r ≠ c` using `hr`.

Use `⟨cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).1, ?_⟩` and prove the remaining obligations. Rewrite using `[cGL_inv_coe]`. Conclude with `cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).2`.
-/
theorem cGL_stab {t₀ : Sub ι m} {p : GL ι R} (hp : p ∈ stab R (t₀.1 : Set ι)) :
    cGL m p ∈ stab R ({t₀} : Set (Sub ι m)) := by
  rw [mem_stab] at hp ⊢
  intro r hr c hc
  have hc' : c = t₀ := hc
  subst hc'
  have hr' : r ≠ c := hr
  refine ⟨cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).1, ?_⟩
  rw [cGL_inv_coe]
  exact cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_coe (f : E →+* R) (δ : GL ι E) :
    ((Matrix.GeneralLinearGroup.map f δ : GL ι R) : Matrix ι ι R) = (δ : Matrix ι ι E).map f := rfl

/- English proof (translation)
Take `⟨δ, rfl⟩` from `hγ`. Establish `key : ∀ δ : GL ι E, (∀ t, t ≠ t₀ → cmp ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) t t₀ = 0) → ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) r c = 0`. Introduce `δ h0 r hr c hc`. Establish `h1 : (δ : Matrix ι ι E) r c = 0`. Use `block_of_cmp (δ : Matrix ι ι E) t₀ (Matrix.isUnits_det_units (cGL m δ)) (fun t ht => ?_) r hr c hc` and prove the remaining obligations.

Establish `h2` using `h0 t ht`. Rewrite `h2` using `[map_coe, cmp_map, Matrix.map_apply]`. Conclude with `hi (by rw [h2, map_zero])`. Rewrite using `[map_coe, Matrix.map_apply, h1, map_zero]`. Rewrite `h`, the goal using `[mem_stab]`.

Introduce `r hr c hc`. Use `⟨key δ (fun t ht => (h t ht t₀ rfl).1) r hr c hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Use `key δ⁻¹ (fun t ht => ?_) r hr c hc` and prove the remaining obligations. Establish `h3` using `(h t ht t₀ rfl).2`.

Rewrite `h3` using `[cGL_inv_coe, ← map_inv]`. Conclude with `h3`.
-/
theorem stab_of_cGL (A : Ad E R) (hi : Function.Injective A.i) {t₀ : Sub ι m} {γ : GL ι R} (hγ : γ ∈ A.ratGL ι)
    (h : cGL m γ ∈ stab R ({t₀} : Set (Sub ι m))) : γ ∈ stab R (t₀.1 : Set ι) := by
  obtain ⟨δ, rfl⟩ := hγ
  have key : ∀ δ : GL ι E, (∀ t, t ≠ t₀ → cmp ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) t t₀ = 0) →
      ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι),
        ((Matrix.GeneralLinearGroup.map A.i δ : GL ι R) : Matrix ι ι R) r c = 0 := by
    intro δ h0 r hr c hc
    have h1 : (δ : Matrix ι ι E) r c = 0 := by
      refine block_of_cmp (δ : Matrix ι ι E) t₀ (Matrix.isUnits_det_units (cGL m δ)) (fun t ht => ?_) r hr c hc
      have h2 := h0 t ht
      rw [map_coe, cmp_map, Matrix.map_apply] at h2
      exact hi (by rw [h2, map_zero])
    rw [map_coe, Matrix.map_apply, h1, map_zero]
  rw [mem_stab] at h ⊢
  intro r hr c hc
  refine ⟨key δ (fun t ht => (h t ht t₀ rfl).1) r hr c hc, ?_⟩
  rw [← map_inv]
  refine key δ⁻¹ (fun t ht => ?_) r hr c hc
  have h3 := (h t ht t₀ rfl).2
  rw [cGL_inv_coe, ← map_inv] at h3
  exact h3

/- English proof (translation)
Take `⟨δ, rfl⟩` from `hγ`. Use `⟨cGL m δ, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[map_coe, cGL_coe, cGL_coe, map_coe, cmp_map]`.
-/
theorem cGL_rat (A : Ad E R) {γ : GL ι R} (hγ : γ ∈ A.ratGL ι) : cGL m γ ∈ A.ratGL (Sub ι m) := by
  obtain ⟨δ, rfl⟩ := hγ
  refine ⟨cGL m δ, Units.ext ?_⟩
  rw [map_coe, cGL_coe, cGL_coe, map_coe, cmp_map]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_kGL (A : Ad E R) {k : GL ι R} : k ∈ A.kGL ι ↔
    (∀ r c, (k : Matrix ι ι R) r c ∈ A.O ∧ ((k⁻¹ : GL ι R) : Matrix ι ι R) r c ∈ A.O) ∧
    ∀ w, (k : Matrix ι ι R).map (A.φ w) ∈ Matrix.unitaryGroup ι ℂ := Iff.rfl

/- English proof (translation)
Rewrite `hk`, the goal using `[mem_kGL]`. Use `⟨fun r c => ⟨cmp_mem A.O _ (fun a b => (hk.1 a b).1) r c, ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[cGL_inv_coe]`. Conclude with `cmp_mem A.O _ (fun a b => (hk.1 a b).2) r c`. Establish `hU` using `hk.2 w`.

Rewrite `hU`, the goal using `[Matrix.mem_unitaryGroup_iff']`. Rewrite using `[cGL_coe, ← cmp_map, star_eq_conjTranspose, ← cmp_conjTranspose, ← cmp_mul, ← star_eq_conjTranspose, hU, cmp_one]`.
-/
theorem cGL_k (A : Ad E R) {k : GL ι R} (hk : k ∈ A.kGL ι) : cGL m k ∈ A.kGL (Sub ι m) := by
  rw [mem_kGL] at hk ⊢
  refine ⟨fun r c => ⟨cmp_mem A.O _ (fun a b => (hk.1 a b).1) r c, ?_⟩, fun w => ?_⟩
  · rw [cGL_inv_coe]
    exact cmp_mem A.O _ (fun a b => (hk.1 a b).2) r c
  · have hU := hk.2 w
    rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
    rw [cGL_coe, ← cmp_map, star_eq_conjTranspose, ← cmp_conjTranspose, ← cmp_mul, ← star_eq_conjTranspose, hU, cmp_one]

/- English proof (translation)
Unfold `bdet`. Distinguish the cases in `h1 : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det`. Establish `h2 : IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det`. Rewrite using `[← h]`. Conclude with `h1`.

Rewrite using `[dif_pos h1, dif_pos h2]`. Conclude with `Units.ext (by simpa using h)`. Establish `h2 : ¬ IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det`. Rewrite using `[← h]`. Conclude with `h1`.

Rewrite using `[dif_neg h1, dif_neg h2]`.
-/
theorem bdet_eq {κ : Type} [Fintype κ] [DecidableEq κ] {s : Set ι} {s' : Set κ} {g : GL ι R} {g' : GL κ R}
    (h : ∀ [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'],
      ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det) : bdet s g = bdet s' g' := by
  classical
  unfold bdet
  by_cases h1 : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det
  · have h2 : IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det := by
      rw [← h]; exact h1
    rw [dif_pos h1, dif_pos h2]
    exact Units.ext (by simpa using h)
  · have h2 : ¬ IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det := by
      rw [← h]; exact h1
    rw [dif_neg h1, dif_neg h2]

/- English proof (translation)
Use `bdet_eq ?_` and prove the remaining obligations. Introduce `_ _ _ _`. Rewrite using `[det_block t₀ _ rfl, det_eq_elem_of_subsingleton _ (⟨t₀, rfl⟩ : ({t₀} : Set (Sub ι m)))]`. Both sides reduce to the same expression.
-/
theorem bdet_cGL (t₀ : Sub ι m) (g : GL ι R) : bdet ({t₀} : Set (Sub ι m)) (cGL m g) = bdet (t₀.1 : Set ι) g := by
  refine bdet_eq ?_
  intro _ _ _ _
  rw [det_block t₀ _ rfl, det_eq_elem_of_subsingleton _ (⟨t₀, rfl⟩ : ({t₀} : Set (Sub ι m)))]
  rfl

end Grp

section Ht

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

/- English proof (translation)
Take `⟨cl, mul, cont, rat, kk, -⟩` from `hB E R A hA ι s`. Use `hE (GL ι R) (A.ratGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) cl (hA.iwa ι s) (fun p hp q hq => ?_) (hA.lgcont.comp_continuousOn cont) (fun p hp hk => kk p hp hk) (fun p hp hΓ => ?_)` and prove the remaining obligations. Simplify using `only [mul p hp q hq, hA.lgmul]`. Take `⟨x, hx⟩` from `rat p hp hΓ`. Simplify using `only [hx, hA.lgi x]`.
-/
theorem ht_law (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι) :
    IsHt (A.ratGL ι) (A.kGL ι) (stab R s) (A.htGL s) ∧
      ∀ p ∈ stab R s, ∀ k ∈ A.kGL ι, A.htGL s (p * k) = A.lg (bdet s p) := by
  obtain ⟨cl, mul, cont, rat, kk, -⟩ := hB E R A hA ι s
  refine hE (GL ι R) (A.ratGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) cl (hA.iwa ι s)
    (fun p hp q hq => ?_) (hA.lgcont.comp_continuousOn cont) (fun p hp hk => kk p hp hk) (fun p hp hΓ => ?_)
  · simp only [mul p hp q hq, hA.lgmul]
  · obtain ⟨x, hx⟩ := rat p hp hΓ
    simp only [hx, hA.lgi x]

/- English proof (translation)
Take `⟨p, hp, k, hk, rfl⟩` from `hA.iwa ι (t₀.1 : Set ι) g`. Rewrite using `[map_mul, (ht_law hB hE A hA _ _).2 _ (cGL_stab hp) _ (cGL_k A hk), bdet_cGL, (ht_law hB hE A hA _ _).2 _ hp _ hk]`.
-/
theorem ht_cGL (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (g : GL ι R) :
    A.htGL ({t₀} : Set (Sub ι m)) (cGL m g) = A.htGL (t₀.1 : Set ι) g := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hA.iwa ι (t₀.1 : Set ι) g
  rw [map_mul, (ht_law hB hE A hA _ _).2 _ (cGL_stab hp) _ (cGL_k A hk), bdet_cGL, (ht_law hB hE A hA _ _).2 _ hp _ hk]

/- English proof (translation)
Introduce `g`. Set `Φ : Cos (stab R (t₀.1 : Set ι)) (A.ratGL ι) → Cos (stab R ({t₀} : Set (Sub ι m))) (A.ratGL (Sub ι m))` to `fun q => Quotient.mk _ ⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩`. Establish `hinj : Function.Injective Φ`. Introduce `q₁ q₂ h`. Establish `h1` using `Quotient.exact h`.

Express the relevant statement in the definitionally equal form `QuotientGroup.rightRel _ _ _ at h1`. Rewrite `h1` using `[QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]`. Establish `h2 : cGL m (rep q₂ * (rep q₁)⁻¹) ∈ stab R ({t₀} : Set (Sub ι m))`. Rewrite using `[map_mul, map_inv]`. Conclude with `h1`.

Establish `h3 : rep q₂ * (rep q₁)⁻¹ ∈ A.ratGL ι` using `mul_mem (Quotient.out q₂).2 (inv_mem (Quotient.out q₁).2)`. Establish `h4` using `stab_of_cGL A hA.iinj h3 h2`. Rewrite using `[← Quotient.out_eq q₁, ← Quotient.out_eq q₂]`. Use `Quotient.sound ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `QuotientGroup.rightRel _ _ _`.

Rewrite using `[QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]`. Conclude with `h4`. Establish `hval : ∀ q, rep (Φ q) * cGL m g = (rep (Φ q) * (cGL m (rep q))⁻¹) * cGL m (rep q * g)`. Introduce `q`. Rewrite using `[map_mul]`.

Use `group`. Establish `hmem : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ stab R ({t₀} : Set (Sub ι m))`. Introduce `q`. Establish `h1` using `Quotient.mk_out (s := QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m)))) (⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩ : A.ratGL (Sub ι m))`. Establish `h2` using `(QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m)))).iseqv.symm h1`.

Express the relevant statement in the definitionally equal form `QuotientGroup.rightRel _ _ _ at h2`. Rewrite `h2` using `[QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]`. Conclude with `h2`. Establish `hrat : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ A.ratGL (Sub ι m)` using `fun q => mul_mem (Quotient.out (Φ q)).2 (inv_mem (cGL_rat A (Quotient.out q).2))`. Establish `H` using `ht_law hB hE A hA (Sub ι m) ({t₀} : Set (Sub ι m))`.

Establish `hs` using `(hx (cGL m g)).comp_injective hinj`. Use `hs.congr fun q => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hval q, H.1.left _ (hmem q), H.1.rat _ (hrat q) (hmem q), zero_add, ht_cGL hB hE A hA]`.
-/
theorem conv_of_line (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (x : ℝ)
    (hx : Conv (A.ratGL (Sub ι m)) (stab R ({t₀} : Set (Sub ι m))) fun g => x * A.htGL ({t₀} : Set (Sub ι m)) g) :
    Conv (A.ratGL ι) (stab R (t₀.1 : Set ι)) fun g => x * A.htGL (t₀.1 : Set ι) g := by
  intro g
  let Φ : Cos (stab R (t₀.1 : Set ι)) (A.ratGL ι) → Cos (stab R ({t₀} : Set (Sub ι m))) (A.ratGL (Sub ι m)) :=
    fun q => Quotient.mk _ ⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩
  have hinj : Function.Injective Φ := by
    intro q₁ q₂ h
    have h1 := Quotient.exact h
    change QuotientGroup.rightRel _ _ _ at h1
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h1
    have h2 : cGL m (rep q₂ * (rep q₁)⁻¹) ∈ stab R ({t₀} : Set (Sub ι m)) := by
      rw [map_mul, map_inv]
      exact h1
    have h3 : rep q₂ * (rep q₁)⁻¹ ∈ A.ratGL ι := mul_mem (Quotient.out q₂).2 (inv_mem (Quotient.out q₁).2)
    have h4 := stab_of_cGL A hA.iinj h3 h2
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    refine Quotient.sound ?_
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
    exact h4
  have hval : ∀ q, rep (Φ q) * cGL m g = (rep (Φ q) * (cGL m (rep q))⁻¹) * cGL m (rep q * g) := by
    intro q
    rw [map_mul]
    group
  have hmem : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ stab R ({t₀} : Set (Sub ι m)) := by
    intro q
    have h1 := Quotient.mk_out (s := QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m))))
      (⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩ : A.ratGL (Sub ι m))
    have h2 := (QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m)))).iseqv.symm h1
    change QuotientGroup.rightRel _ _ _ at h2
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hrat : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ A.ratGL (Sub ι m) := fun q =>
    mul_mem (Quotient.out (Φ q)).2 (inv_mem (cGL_rat A (Quotient.out q).2))
  have H := ht_law hB hE A hA (Sub ι m) ({t₀} : Set (Sub ι m))
  have hs := (hx (cGL m g)).comp_injective hinj
  refine hs.congr fun q => ?_
  simp only [Function.comp_apply]
  rw [hval q, H.1.left _ (hmem q), H.1.rat _ (hrat q) (hmem q), zero_add, ht_cGL hB hE A hA]

/- English proof (translation)
Substitute `hP` using the available equality. Introduce `g`. Use `haveI : Subsingleton (Cos (⊤ : Subgroup G) Γ) := ⟨fun a b => by`. Proceed by induction on `a using Quotient.inductionOn with | _ x => ?_`. Proceed by induction on `b using Quotient.inductionOn with | _ y => ?_`.

Use `Quotient.sound ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `QuotientGroup.rightRel _ _ _`. Rewrite using `[QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]`. Use the proof step `trivial⟩`. Conclude with `summable_of_finite_support (Set.toFinite _)`.
-/
theorem conv_top {G : Type} [Group G] (Γ P : Subgroup G) (hP : P = ⊤) (l : G → ℝ) : Conv Γ P l := by
  subst hP
  intro g
  haveI : Subsingleton (Cos (⊤ : Subgroup G) Γ) := ⟨fun a b => by
    induction a using Quotient.inductionOn with | _ x => ?_
    induction b using Quotient.inductionOn with | _ y => ?_
    refine Quotient.sound ?_
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
    trivial⟩
  exact summable_of_finite_support (Set.toFinite _)

end Ht

/- English proof (translation)
Introduce `hB hE E R _ _ _ _ _ _ _ A hA hM ι _ _ s`. Distinguish the cases in `h0 : s = ∅`. Substitute `h0` using the available equality. Use `⟨0, fun x _ => conv_top _ _ ?_ _⟩` and prove the remaining obligations. Use extensionality with `g`.

Simplify using `[mem_stab]`. Distinguish the cases in `h1 : s = Set.univ`. Substitute `h1` using the available equality. Use `⟨0, fun x _ => conv_top _ _ ?_ _⟩` and prove the remaining obligations. Use extensionality with `g`.

Simplify using `[mem_stab]`. Take `⟨f, rfl⟩ : ∃ f : Finset ι, (f : Set ι) = s` from `⟨(Set.toFinite s).toFinset, by simp⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, c ∈ f := by`. Assume the negation of the conclusion as `hne`. Conclude with `h0 (by ext x; simp; exact fun hx => hne ⟨x, hx⟩)`.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, r ∉ f := by`. Assume the negation of the conclusion as `hne`. Conclude with `h1 (by ext x; simp; by_contra hx; exact hne ⟨x, hx⟩)`. Set `t₀ : Sub ι (Fin f.card)` to `⟨f, by simp [Set.powersetCard]⟩`. Set `t₁ : Sub ι (Fin f.card)` to `⟨insert r (f.erase c), by`.

Establish `: (insert r (f.erase c)).card = f.card`. Rewrite using `[Finset.card_insert_of_notMem (fun h => hr (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hc]`. Use `Finset.card_pos.2 ⟨c, hc⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify `this⟩` using `[Set.powersetCard]`.

Establish `hne : t₀ ≠ t₁`. Introduce `e`. Establish `h2 : r ∈ t₁.1` using `Finset.mem_insert_self _ _`. Rewrite `h2` using `[← e]`. Conclude with `hr h2`.

Establish `h2 : 2 ≤ Fintype.card (Sub ι (Fin f.card))` using `Fintype.one_lt_card_iff.2 ⟨t₀, t₁, hne⟩`. Take `⟨R₀, D, Op, H, hW, -⟩` from `(hM (Sub ι (Fin f.card)) t₀ t₀ h2).1 ℂ 1 continuous_const`. Conclude with `⟨R₀, fun x hx => conv_of_line hB hE A hA.toGoodL t₀ x (hW.convR x hx)⟩`.
-/
theorem convGrOf : BdetLaw → ExtLaw → ConvGrOf := by
  intro hB hE E R _ _ _ _ _ _ _ A hA hM ι _ _ s
  by_cases h0 : s = ∅
  · subst h0
    refine ⟨0, fun x _ => conv_top _ _ ?_ _⟩
    ext g
    simp [mem_stab]
  by_cases h1 : s = Set.univ
  · subst h1
    refine ⟨0, fun x _ => conv_top _ _ ?_ _⟩
    ext g
    simp [mem_stab]
  obtain ⟨f, rfl⟩ : ∃ f : Finset ι, (f : Set ι) = s := ⟨(Set.toFinite s).toFinset, by simp⟩
  obtain ⟨c, hc⟩ : ∃ c, c ∈ f := by
    by_contra hne
    exact h0 (by ext x; simp; exact fun hx => hne ⟨x, hx⟩)
  obtain ⟨r, hr⟩ : ∃ r, r ∉ f := by
    by_contra hne
    exact h1 (by ext x; simp; by_contra hx; exact hne ⟨x, hx⟩)
  let t₀ : Sub ι (Fin f.card) := ⟨f, by simp [Set.powersetCard]⟩
  let t₁ : Sub ι (Fin f.card) := ⟨insert r (f.erase c), by
    have : (insert r (f.erase c)).card = f.card := by
      rw [Finset.card_insert_of_notMem (fun h => hr (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hc]
      have := Finset.card_pos.2 ⟨c, hc⟩
      omega
    simpa [Set.powersetCard] using this⟩
  have hne : t₀ ≠ t₁ := by
    intro e
    have h2 : r ∈ t₁.1 := Finset.mem_insert_self _ _
    rw [← e] at h2
    exact hr h2
  have h2 : 2 ≤ Fintype.card (Sub ι (Fin f.card)) := Fintype.one_lt_card_iff.2 ⟨t₀, t₁, hne⟩
  obtain ⟨R₀, D, Op, H, hW, -⟩ := (hM (Sub ι (Fin f.card)) t₀ t₀ h2).1 ℂ 1 continuous_const
  exact ⟨R₀, fun x hx => conv_of_line hB hE A hA.toGoodL t₀ x (hW.convR x hx)⟩

end GlobalTheory.CompanionTheory.Plucker
