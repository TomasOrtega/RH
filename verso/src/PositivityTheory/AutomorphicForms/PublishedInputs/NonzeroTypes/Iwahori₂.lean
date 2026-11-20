import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace Iwahori₂

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩`.
-/
theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

/- English proof (translation)
Take `⟨x', hx', rfl⟩` from `hx`. Take `⟨y', hy', rfl⟩` from `hy`. Conclude with `⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', map_mul _ _ _⟩`.
-/
theorem inPow_mul {a b : ℕ} {x y : k} (hx : InPow a x) (hy : InPow b y) : InPow (a + b) (x * y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', map_mul _ _ _⟩

/- English proof (translation)
Take `⟨x', hx', rfl⟩` from `hx`. Take `⟨y', hy', rfl⟩` from `hy`. Conclude with `⟨x' + y', add_mem hx' hy', map_add _ _ _⟩`.
-/
theorem inPow_add {a : ℕ} {x y : k} (hx : InPow a x) (hy : InPow a y) : InPow a (x + y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, zero_mem _, map_zero _⟩`.
-/
theorem inPow_zero (a : ℕ) : InPow a (0 : k) := ⟨0, zero_mem _, map_zero _⟩

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simpa using inPow_zero (k := k) a`. Consider the case `cons i s hi ih`. Rewrite using `[Finset.sum_cons]`. Conclude with `inPow_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))`.
-/
theorem inPow_sum {a : ℕ} {ι : Type} (s : Finset ι) (f : ι → k) (h : ∀ i ∈ s, InPow a (f i)) :
    InPow a (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using inPow_zero (k := k) a
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact inPow_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/- English proof (translation)
Take `⟨g', rfl⟩` from `hg`. Conclude with `⟨(g' : Matrix (Fin n) (Fin n) 𝒪[k]) i j, by simp, rfl⟩`.
-/
theorem inPow_zero_of_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) :
    InPow 0 ((g : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨g', rfl⟩ := hg
  exact ⟨(g' : Matrix (Fin n) (Fin n) 𝒪[k]) i j, by simp, rfl⟩

/- English proof (translation)
Rewrite using `[mem_unipRadLower, mem_parabLower_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j`. Take `⟨⟨a, i'⟩, rfl⟩` from `G.e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `G.e.surjective j`.

Simplify using `only [Grp.bl, Equiv.symm_apply_apply]`. Use `⟨fun h => h1 a b i' j' h, fun h => ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality. Rewrite using `[h2 a i' j', Matrix.one_apply]`. Simplify using the standard rewrite rules.

Introduce `h`. Use `⟨fun a b i' j' hab => (h _ _).1 (by simpa [Grp.bl] using hab), fun a i' j' => ?_⟩` and prove the remaining obligations. Rewrite using `[(h _ _).2 (by simp [Grp.bl]), Matrix.one_apply]`. Simplify using the standard rewrite rules.
-/
theorem mem_uRL {R : Type} [CommRing R] (X : GL (Fin n) R) :
    X ∈ unipRadLower R G.e ↔ ∀ i j, (G.bl i < G.bl j → (X : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      (G.bl i = G.bl j → (X : Matrix (Fin n) (Fin n) R) i j = if i = j then 1 else 0) := by
  rw [mem_unipRadLower, mem_parabLower_iff]
  constructor
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
    simp only [Grp.bl, Equiv.symm_apply_apply]
    refine ⟨fun h => h1 a b i' j' h, fun h => ?_⟩
    subst h
    rw [h2 a i' j', Matrix.one_apply]
    simp
  · intro h
    refine ⟨fun a b i' j' hab => (h _ _).1 (by simpa [Grp.bl] using hab), fun a i' j' => ?_⟩
    rw [(h _ _).2 (by simp [Grp.bl]), Matrix.one_apply]
    simp

abbrev Lt (b : Fin G.s) : Type := {j : Fin n // G.bl j < b}

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (b : ℕ) with hb | hb` into its components or cases. Establish `: IsEmpty (Lt G b)` using `⟨fun j => by`. Use `j.2` as an intermediate fact. Rewrite `this` using `[Fin.lt_def]`. Use the proof step `omega⟩`.

Rewrite using `[Matrix.det_isEmpty]`. Conclude with `isUnit_one`. Set `a : Fin G.s` to `⟨b - 1, by omega⟩`. Take `⟨u, hu⟩` from `hA a`. Establish `hiff : ∀ j : Fin n, G.bl j ≤ a ↔ G.bl j < b` using `fun j => by`.

Simplify using `only [Fin.le_def, Fin.lt_def, a]`. Use linear arithmetic over natural numbers and integers. Set `f : {j : Fin n // G.bl j ≤ a} ≃ Lt G b` to `Equiv.subtypeEquivRight hiff`. Rewrite using `[← Matrix.det_submatrix_equiv_self f]`. Establish `h2 : algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix (Subtype.val : {j : Fin n // G.bl j ≤ a} → Fin n) Subtype.val).det = algebraMap 𝒪[k] k u`.

Rewrite using `[← hu, Grp.Δ, RingHom.map_det]`. Both sides reduce to the same expression. Establish `h3` using `Subtype.val_injective h2`. Use `u.isUnit using 2` and compare the differences between its conclusion and the goal. Conclude with `h3`.
-/
theorem isUnit_det_lt (A : GL (Fin n) 𝒪[k])
    (hA : ∀ a, ∃ u : 𝒪[k]ˣ, G.Δ a (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A) =
      algebraMap 𝒪[k] k u) (b : Fin G.s) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix (Subtype.val : Lt G b → Fin n) Subtype.val).det := by
  rcases Nat.eq_zero_or_pos (b : ℕ) with hb | hb
  · have : IsEmpty (Lt G b) := ⟨fun j => by
      have := j.2
      rw [Fin.lt_def] at this
      omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  · let a : Fin G.s := ⟨b - 1, by omega⟩
    obtain ⟨u, hu⟩ := hA a
    have hiff : ∀ j : Fin n, G.bl j ≤ a ↔ G.bl j < b := fun j => by
      simp only [Fin.le_def, Fin.lt_def, a]
      omega
    let f : {j : Fin n // G.bl j ≤ a} ≃ Lt G b := Equiv.subtypeEquivRight hiff
    rw [← Matrix.det_submatrix_equiv_self f]
    have h2 : algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
        (Subtype.val : {j : Fin n // G.bl j ≤ a} → Fin n) Subtype.val).det = algebraMap 𝒪[k] k u := by
      rw [← hu, Grp.Δ, RingHom.map_det]
      rfl
    have h3 := Subtype.val_injective h2
    convert u.isUnit using 2
    exact h3

variable {G}

def rowv (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i : Fin n) : Lt G (G.bl i) → 𝒪[k] :=
  -(Matrix.vecMul (fun j : Lt G (G.bl i) => M i j.1)
    (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val)⁻¹)

variable (G) in

def Wm (M : Matrix (Fin n) (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k] :=
  Matrix.of fun i l => if h : G.bl l < G.bl i then rowv M i ⟨l, h⟩ else (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i l

/- English proof (translation)
Establish `h1 : ¬ G.bl l < G.bl i` using `not_lt.2 h.le`. Establish `h2 : i ≠ l` using `fun e => by subst e; exact lt_irrefl _ h`. Simplify using `[Wm, h1, Matrix.one_apply_ne h2]`.
-/
theorem Wm_upper (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i l : Fin n) (h : G.bl i < G.bl l) : Wm G M i l = 0 := by
  have h1 : ¬ G.bl l < G.bl i := not_lt.2 h.le
  have h2 : i ≠ l := fun e => by subst e; exact lt_irrefl _ h
  simp [Wm, h1, Matrix.one_apply_ne h2]

/- English proof (translation)
Establish `h1 : ¬ G.bl l < G.bl i` using `by rw [h]; exact lt_irrefl _`. Simplify using `[Wm, h1, Matrix.one_apply]`.
-/
theorem Wm_diag (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i l : Fin n) (h : G.bl i = G.bl l) :
    Wm G M i l = if i = l then 1 else 0 := by
  have h1 : ¬ G.bl l < G.bl i := by rw [h]; exact lt_irrefl _
  simp [Wm, h1, Matrix.one_apply]

/- English proof (translation)
Establish `hb : (Wm G M).BlockTriangular (fun i => OrderDual.toDual (G.bl i))` using `fun i l h => Wm_upper M i l (OrderDual.toDual_lt_toDual.1 h)`. Rewrite using `[hb.det_fintype]`. Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Establish `: (Wm G M).toSquareBlock (fun i => OrderDual.toDual (G.bl i)) c = 1`. Use `Matrix.ext fun x y => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply]`. Rewrite using `[Wm_diag M x.1 y.1 (by simpa using x.2.trans y.2.symm)]`. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem det_Wm (M : Matrix (Fin n) (Fin n) 𝒪[k]) : (Wm G M).det = 1 := by
  have hb : (Wm G M).BlockTriangular (fun i => OrderDual.toDual (G.bl i)) := fun i l h =>
    Wm_upper M i l (OrderDual.toDual_lt_toDual.1 h)
  rw [hb.det_fintype]
  refine Finset.prod_eq_one fun c _ => ?_
  have : (Wm G M).toSquareBlock (fun i => OrderDual.toDual (G.bl i)) c = 1 := by
    refine Matrix.ext fun x y => ?_
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [Wm_diag M x.1 y.1 (by simpa using x.2.trans y.2.symm)]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

/- English proof (translation)
Establish `hs` using `Fintype.sum_subtype_add_sum_subtype (fun l => G.bl l < G.bl i) (fun l => Wm G M i l * M l j)`. Establish `h1 : ∑ l : Lt G (G.bl i), Wm G M i l.1 * M l.1 j = Matrix.vecMul (rowv M i) (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val) (⟨j, hij⟩ : Lt G (G.bl i))`. Simplify using `only [Matrix.vecMul, dotProduct, Wm, Matrix.of_apply, Matrix.submatrix_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos l.2]`.

Establish `h2 : ∑ l : {l : Fin n // ¬ G.bl l < G.bl i}, Wm G M i l.1 * M l.1 j = M i j`. Rewrite using `[Finset.sum_eq_single ⟨i, lt_irrefl _⟩]`. Simplify using `[Wm]`. Introduce `l _ hl`. Establish `: l.1 ≠ i` using `fun h => hl (Subtype.ext h)`.

Simplify using `[Wm, l.2, Matrix.one_apply_ne' this]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Matrix.mul_apply, ← hs]`. Use `erw [h1, h2]`.

Rewrite using `[rowv, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Simplify using the standard rewrite rules.
-/
theorem Wm_mul (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i j : Fin n) (hij : G.bl j < G.bl i)
    (hu : IsUnit (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val).det) :
    (Wm G M * M) i j = 0 := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun l => G.bl l < G.bl i) (fun l => Wm G M i l * M l j)
  have h1 : ∑ l : Lt G (G.bl i), Wm G M i l.1 * M l.1 j =
      Matrix.vecMul (rowv M i) (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val) (⟨j, hij⟩ : Lt G (G.bl i)) := by
    simp only [Matrix.vecMul, dotProduct, Wm, Matrix.of_apply, Matrix.submatrix_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dif_pos l.2]
  have h2 : ∑ l : {l : Fin n // ¬ G.bl l < G.bl i}, Wm G M i l.1 * M l.1 j = M i j := by
    rw [Finset.sum_eq_single ⟨i, lt_irrefl _⟩]
    · simp [Wm]
    · intro l _ hl
      have : l.1 ≠ i := fun h => hl (Subtype.ext h)
      simp [Wm, l.2, Matrix.one_apply_ne' this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply, ← hs]
  erw [h1, h2]
  rw [rowv, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  simp

/- English proof (translation)
Rewrite `hp`, the goal using `[GlobalTheory.StepData.mem_KO]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[leviProj_apply]`. Conclude with `hp.1 _ _`. Establish `hinv : (leviProj k (stdBlocks d hd) p a)⁻¹ = leviProj k (stdBlocks d hd) p⁻¹ a`.

Rewrite using `[map_inv, Pi.inv_apply]`. Rewrite using `[hinv, leviProj_apply]`. Conclude with `hp.2 _ _`.
-/
theorem leviProj_mem_KO {s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [leviProj_apply]
    exact hp.1 _ _
  · have hinv : (leviProj k (stdBlocks d hd) p a)⁻¹ = leviProj k (stdBlocks d hd) p⁻¹ a := by
      rw [map_inv, Pi.inv_apply]
    rw [hinv, leviProj_apply]
    exact hp.2 _ _

variable (G)

/- English proof (translation)
Introduce `g hg`. Establish `hΔg` using `hΔ g hg`. Take `⟨A, hA⟩` from `MonoidHom.mem_range.1 hg.1`. Substitute `hA` using the available equality. Use `set φ := Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) with hφ`.

Use `set M : Matrix (Fin n) (Fin n) 𝒪[k] := (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM`. Establish `hunit` using `isUnit_det_lt G A hΔg`. Set `W : GL (Fin n) 𝒪[k]` to `Matrix.nonsingInvUnit (Wm G M) (by rw [det_Wm]; exact isUnit_one)`. Establish `hWval : (W : Matrix (Fin n) (Fin n) 𝒪[k]) = Wm G M` using `rfl`. Establish `hWL : W ∈ unipRadLower 𝒪[k] G.e` using `(mem_uRL G W).2 fun i j => ⟨Wm_upper M i j, Wm_diag M i j⟩`.

Establish `hP : ∀ i j, G.bl j < G.bl i → ((W * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j = 0` using `fun i j h => by rw [Units.val_mul, hWval]; exact Wm_mul M i j h (hunit _)`. Apply the tactic sequence `have hentry : ∀ X : GL (Fin n) 𝒪[k], ∀ i j, ((φ X : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((X : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := fun _ _ _ => rfl`. Use `set p := φ (W * A) with hp`. Use `set v := φ W⁻¹ with hv`. Establish `hpP : p ∈ parab k G.e` using `mem_parab.2 fun i j h => by rw [hentry, hP i j h, map_zero]`.

Establish `hpK : p ∈ KO k (Fin n)` using `⟨W * A, rfl⟩`. Establish `hvK : v ∈ KO k (Fin n)` using `⟨W⁻¹, rfl⟩`. Establish `hgvp : φ A = v * p` using `by rw [hv, hp, ← map_mul, inv_mul_cancel_left]`. Establish `hvN : v ∈ G.Nbar`. Establish `h` using `(mem_uRL G W⁻¹).1 (inv_mem hWL)`.

Introduce `i j`. Use `⟨fun hij => by rw [hentry, (h i j).1 hij, map_zero], fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hentry, (h i j).2 hij]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hvJ : v ∈ G.JSet`.

Use `⟨hvK, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `hv' : v = φ A * p⁻¹` using `by rw [hgvp, mul_inv_cancel_right]`. Rewrite using `[hv', Units.val_mul, Matrix.mul_apply]`. Use `inPow_sum _ _ fun l _ => ?_` and prove the remaining obligations. Break down `le_or_gt (G.bl l) (G.bl j) with hl | hl` into its components or cases.

Establish `h1` using `hg.2 i l (lt_of_le_of_lt hl hij)`. Establish `h3` using `inPow_mul h1 (inPow_zero_of_KO (inv_mem hpK) l j)`. Rewrite `h3` using `[add_zero]`. Conclude with `inPow_mono (G.ball _ _ _ _ hl hij le_rfl) h3`. Rewrite using `[mem_parab.1 (inv_mem hpP) l j hl, mul_zero]`.

Conclude with `inPow_zero _`. Set `pp : parab k G.e` to `⟨p, hpP⟩`. Establish `hm : leviProj k G.e pp ∈ leviK k (m` using `fun a : Fin G.s => Fin (G.d a)) := (Subgroup.mem_pi _).2 fun a _ => leviProj_mem_KO G.d G.hd pp hpK a`. Take `⟨u, hu, hpu⟩` from `exists_levi_mul_unip k G.e pp`. Establish `hE` using `leviEmb_mem_KO G.e hm`.

Establish `huK : u ∈ KO k (Fin n)`. Establish `: u = (leviEmb k G.e (leviProj k G.e pp))⁻¹ * p`. Rewrite using `[eq_inv_mul_iff_mul_eq]`. Conclude with `hpu.symm`. Rewrite using `[this]`.

Conclude with `mul_mem (inv_mem hE) hpK`. Use `⟨v, hvN, hvJ, leviProj k G.e pp, hm, u, ⟨hu, huK⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hgvp, mul_assoc, ← hpu]`.
-/
theorem iwahori_of (hΔ : ∀ g ∈ G.JSet, ∀ a, ∃ u : 𝒪[k]ˣ, G.Δ a g = algebraMap 𝒪[k] k u) :
    ∀ g ∈ G.JSet, ∃ v ∈ G.Nbar, v ∈ G.JSet ∧
      ∃ m : Levi k (fun a : Fin G.s => Fin (G.d a)), m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) ∧
        ∃ u ∈ G.NO, g = v * leviEmb k G.e m * u := by
  intro g hg
  have hΔg := hΔ g hg
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hg.1
  subst hA
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) with hφ
  set M : Matrix (Fin n) (Fin n) 𝒪[k] := (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hunit := isUnit_det_lt G A hΔg
  let W : GL (Fin n) 𝒪[k] := Matrix.nonsingInvUnit (Wm G M) (by rw [det_Wm]; exact isUnit_one)
  have hWval : (W : Matrix (Fin n) (Fin n) 𝒪[k]) = Wm G M := rfl
  have hWL : W ∈ unipRadLower 𝒪[k] G.e :=
    (mem_uRL G W).2 fun i j => ⟨Wm_upper M i j, Wm_diag M i j⟩
  have hP : ∀ i j, G.bl j < G.bl i → ((W * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j = 0 :=
    fun i j h => by rw [Units.val_mul, hWval]; exact Wm_mul M i j h (hunit _)
  have hentry : ∀ X : GL (Fin n) 𝒪[k], ∀ i j, ((φ X : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      algebraMap 𝒪[k] k ((X : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := fun _ _ _ => rfl
  set p := φ (W * A) with hp
  set v := φ W⁻¹ with hv
  have hpP : p ∈ parab k G.e := mem_parab.2 fun i j h => by rw [hentry, hP i j h, map_zero]
  have hpK : p ∈ KO k (Fin n) := ⟨W * A, rfl⟩
  have hvK : v ∈ KO k (Fin n) := ⟨W⁻¹, rfl⟩
  have hgvp : φ A = v * p := by rw [hv, hp, ← map_mul, inv_mul_cancel_left]
  have hvN : v ∈ G.Nbar := by
    have h := (mem_uRL G W⁻¹).1 (inv_mem hWL)
    intro i j
    refine ⟨fun hij => by rw [hentry, (h i j).1 hij, map_zero], fun hij => ?_⟩
    rw [hentry, (h i j).2 hij]
    split_ifs <;> simp
  have hvJ : v ∈ G.JSet := by
    refine ⟨hvK, fun i j hij => ?_⟩
    have hv' : v = φ A * p⁻¹ := by rw [hgvp, mul_inv_cancel_right]
    rw [hv', Units.val_mul, Matrix.mul_apply]
    refine inPow_sum _ _ fun l _ => ?_
    rcases le_or_gt (G.bl l) (G.bl j) with hl | hl
    · have h1 := hg.2 i l (lt_of_le_of_lt hl hij)
      have h3 := inPow_mul h1 (inPow_zero_of_KO (inv_mem hpK) l j)
      rw [add_zero] at h3
      exact inPow_mono (G.ball _ _ _ _ hl hij le_rfl) h3
    · rw [mem_parab.1 (inv_mem hpP) l j hl, mul_zero]
      exact inPow_zero _
  let pp : parab k G.e := ⟨p, hpP⟩
  have hm : leviProj k G.e pp ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) :=
    (Subgroup.mem_pi _).2 fun a _ => leviProj_mem_KO G.d G.hd pp hpK a
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k G.e pp
  have hE := leviEmb_mem_KO G.e hm
  have huK : u ∈ KO k (Fin n) := by
    have : u = (leviEmb k G.e (leviProj k G.e pp))⁻¹ * p := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hpu.symm
    rw [this]
    exact mul_mem (inv_mem hE) hpK
  refine ⟨v, hvN, hvJ, leviProj k G.e pp, hm, u, ⟨hu, huK⟩, ?_⟩
  rw [hgvp, mul_assoc, ← hpu]

end Iwahori₂

/- English proof (translation)
Introduce `_ hcc hΔ _ _`. Conclude with `Iwahori₂.iwahori_of G (hΔ hcc)`.
-/
theorem step_iwahori : IwahoriDecompositionProp G := by
  intro _ hcc hΔ _ _
  exact Iwahori₂.iwahori_of G (hΔ hcc)

end UpperTheory.TNZ.Grp
