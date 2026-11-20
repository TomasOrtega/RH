import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
/- English proof (translation)
Establish `k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0` using `fun x y hx hy => by`. Establish `: x * y ∈ maximalIdeal R * RingHom.ker p` using `Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy`. Rewrite `this` using `[hs, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `z1 : ∀ a b, p (Z a b) = 0` using `fun a b => congrFun (congrFun hZ a) b`. Establish `z2 : ∀ a b, res O R (Z a b) = 0` using `fun a b => by rw [← res_map p, z1, map_zero]`.

Establish `h1 : ∀ a b, res O R ((h - 1) a b) = 0` using `fun a b => by`. Use `congrFun (congrFun hh a) b` as an intermediate fact. Simplify using `only [map_apply] at this`. Rewrite using `[Matrix.sub_apply, map_sub, this]`. Distinguish the cases in `e : a = b`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[one_apply_ne e]`. Establish `K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) → Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0` using `fun A B hA hB => by`. Prove the components needed by the constructor for the conclusion.

Use extensionality with `a b`. Simplify using `only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]`. Use extensionality with `a b`.

Simplify using `only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]`. Prove the components needed by the constructor for the conclusion. Take `⟨e1, e2⟩` from `K (h - 1) Z h1 z1`.

Take `⟨e3, -⟩` from `K Z Z z2 z1`. Rewrite `e1` using `[transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero]`. Rewrite `e2` using `[mul_sub, mul_one, sub_eq_zero]`. Rewrite using `[transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]`. Normalize the expressions using the abelian group laws.

Use extensionality with `a b`. Use `congrFun (congrFun hh a) b` as an intermediate fact. Simplify using `only [map_apply] at this`. Rewrite using `[map_apply, Matrix.add_apply, map_add, z2, add_zero, this]`.
-/
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add, z2, add_zero, this]

open Matrix in
/- English proof (translation)
Introduce `O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `h' ⟨a1, a2, a3⟩`. Use `choose s hs' using hp`. Choose the witnesses or unpack the hypotheses as in `⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by`.

Use `⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩` and prove the remaining obligations. Use extensionality with `a b`. Distinguish the cases in `e : Φ.blk a = Φ.blk b`. Simplify using `[e, hs']`. Simplify using `[e, a2 a b e]`.

Establish `b3 : h0.map (res O R) = 1`. Rewrite using `[← a3, ← b1]`. Use extensionality with `a b`. Simplify using `[res_map]`. Establish `jp : (Φ.JR R).map p = Φ.JR R'`.

Use extensionality with `a b`. Simplify using `[FormData.JR]`. Establish `jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a)` using `fun a b e => Φ.hblk a b fun n => e (by simp [FormData.JR, n])`. Take `⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1` from `(Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by`.

Use `(h2.map (algebraMap O R)).exists_right_inv` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by`. Break down `Φ.sym with e | e` into its components or cases. Use `⟨1, ?_, by simp⟩` and prove the remaining obligations.

Use extensionality with `a b`. Use `congrFun (congrFun e a) b` as an intermediate fact. Simplify using `only [transpose_apply] at this`. Simplify using `[FormData.JR, this]`. Use `⟨-1, ?_, by simp⟩` and prove the remaining obligations.

Use extensionality with `a b`. Use `congrFun (congrFun e a) b` as an intermediate fact. Simplify using `only [transpose_apply] at this`. Simplify using `[FormData.JR, this]`. Use `set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE`.

Establish `E1 : E.map p = 0`. Rewrite using `[hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]`. Establish `E2 : Eᵀ = ε • E`. Rewrite using `[hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]`. Simplify using `[mul_assoc]`.

Establish `E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0` using `fun a b e => by`. Establish `: Φ.JR R a b = 0` using `by_contra fun n => e (jb a b n)`. Rewrite using `[hE, Matrix.sub_apply, this, sub_zero]`. Simplify using `only [mul_apply, transpose_apply, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations.

Distinguish the cases in `e1 : Φ.blk d = Φ.blk a`. Distinguish the cases in `e2 : Φ.blk c = Φ.blk b`. Establish `: Φ.JR R d c = 0` using `by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)`. Simplify using `[this]`. Simplify using `[b2 _ _ e2]`.

Simplify using `[b2 _ _ e1]`. Use `set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0`. Establish `Z1 : Φ.JR R * Z0 = (-u) • E` using `by rw [hZ0, ← mul_assoc, hK, one_mul]`. Establish `Z2 : ∀ a b, p (Z0 a b) = 0` using `fun a b => by`. Rewrite using `[hZ0, mul_apply, map_sum]`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Establish `: p (E c b) = 0` using `congrFun (congrFun E1 c) b`. Simplify using `[this]`. Set `Z : Matrix ι ι R` to `Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0`. Establish `Z3 : Z.map p = 0`.

Use extensionality with `a b`. Apply the tactic sequence `by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]`. Establish `Z4 : Φ.JR R * Z = (-u) • E`. Use extensionality with `a b`. Distinguish the cases in `e : Φ.blk b = Φ.σ (Φ.blk a)`.

Rewrite using `[← Z1, mul_apply, mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `n : Φ.JR R a c = 0`. Simplify using `[n]`. Establish `: Φ.blk c = Φ.blk b` using `by rw [e]; exact jb a c n`.

Simplify using `[Z, this]`. Rewrite using `[Matrix.smul_apply, E3 a b e, smul_zero, mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `n : Φ.JR R a c = 0`. Simplify using `[n]`.

Establish `: ¬ Φ.blk c = Φ.blk b` using `fun m => e (by rw [← m]; exact jb a c n)`. Simplify using `[Z, this]`. Establish `Z5 : Zᵀ * Φ.JR R = (-u) • E`. Use `congrArg (fun M => ε • Mᵀ) Z4` as an intermediate fact. Simplify using `only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this`.

Rewrite `this` using `[hε2, one_smul, mul_left_comm, hε2, mul_one]`. Conclude with `this`. Take `⟨c1, c2⟩` from `expand_small p hs (Φ.JR R) h0 Z b3 Z3`. Use `⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]`.

Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.map_add _ (map_add p), b1, Z3, add_zero]`. Introduce and unpack `h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e`. Establish `hZ : (h₂ - h₁).map p = 0` using `by rw [Matrix.map_sub _ (map_sub p), e, sub_self]`. Take `⟨c1, -⟩` from `expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ`.

Rewrite `c1` using `[add_sub_cancel, a1, b1, left_eq_add]`. Conclude with `⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩`. Introduce and unpack `h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e`. Take `⟨c1, c2⟩` from `expand_small p hs (Φ.JR R) h Y a3 e`. Conclude with `⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩`.
-/
theorem UpperTheory.V.Alg.hh_small :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
      (∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') ∧
      (∀ h₁ h₂ : Matrix ι ι R, Φ.HH h₁ → Φ.HH h₂ → h₁.map p = h₂.map p → h₂ - h₁ ∈ Φ.g R) ∧
      ∀ h Y : Matrix ι ι R, Φ.HH h → Y ∈ Φ.g R → Y.map p = 0 → Φ.HH (h + Y) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs
  refine ⟨?_, ?_, ?_⟩
  · classical
    rintro h' ⟨a1, a2, a3⟩
    choose s hs' using hp
    obtain ⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by
      refine ⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩
      ext a b
      by_cases e : Φ.blk a = Φ.blk b
      · simp [e, hs']
      · simp [e, a2 a b e]
    have b3 : h0.map (res O R) = 1 := by
      rw [← a3, ← b1]
      ext a b
      simp [res_map]
    have jp : (Φ.JR R).map p = Φ.JR R' := by
      ext a b
      simp [FormData.JR]
    have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
      Φ.hblk a b fun n => e (by simp [FormData.JR, n])
    obtain ⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1 :=
      (Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv
    obtain ⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by
      have := (h2.map (algebraMap O R)).exists_right_inv
      rwa [map_ofNat] at this
    obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
      rcases Φ.sym with e | e
      · refine ⟨1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
      · refine ⟨-1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
    set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
    have E1 : E.map p = 0 := by
      rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
    have E2 : Eᵀ = ε • E := by
      rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
      simp [mul_assoc]
    have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
      have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
      rw [hE, Matrix.sub_apply, this, sub_zero]
      simp only [mul_apply, transpose_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      by_cases e1 : Φ.blk d = Φ.blk a
      · by_cases e2 : Φ.blk c = Φ.blk b
        · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
          simp [this]
        · simp [b2 _ _ e2]
      · simp [b2 _ _ e1]
    set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
    have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
    have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by
      rw [hZ0, mul_apply, map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have : p (E c b) = 0 := congrFun (congrFun E1 c) b
      simp [this]
    let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
    have Z3 : Z.map p = 0 := by
      ext a b
      by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
    have Z4 : Φ.JR R * Z = (-u) • E := by
      ext a b
      by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
      · rw [← Z1, mul_apply, mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
          simp [Z, this]
      · rw [Matrix.smul_apply, E3 a b e, smul_zero, mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
          simp [Z, this]
    have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
      have := congrArg (fun M => ε • Mᵀ) Z4
      simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
      rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
      exact this
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
    refine ⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
    · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
      abel
    · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]
  · rintro h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e
    have hZ : (h₂ - h₁).map p = 0 := by rw [Matrix.map_sub _ (map_sub p), e, sub_self]
    obtain ⟨c1, -⟩ := expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ
    rw [add_sub_cancel, a1, b1, left_eq_add] at c1
    exact ⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩
  · rintro h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h Y a3 e
    exact ⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩
