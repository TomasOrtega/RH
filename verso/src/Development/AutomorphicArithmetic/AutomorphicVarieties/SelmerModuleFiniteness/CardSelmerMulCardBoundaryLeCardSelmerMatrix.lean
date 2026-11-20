import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Set `E : Matrix (Fin n) (Fin n) X` to `Matrix.diagonal fun k => if (k : ℕ) < x.a then 1 else 0`. Set `E' : Matrix (Fin n) (Fin n) X` to `Matrix.diagonal fun k => if x.ty v k then 1 else 0`. Establish `hwi : x.wiX X v * x.wX X v = 1`. Simplify using `only [NP.wiX, NP.wX]`. Rewrite using `[← Matrix.map_mul, (x.w v).inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hw' : x.wX X v * x.wiX X v = 1`. Simplify using `only [NP.wiX, NP.wX]`. Rewrite using `[← Matrix.map_mul, (x.w v).mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hEw : E * x.wX X v = x.wX X v * E'`. Use extensionality with `i j`.

Simplify using `only [E, E', Matrix.diagonal_mul, Matrix.mul_diagonal, NP.wX, Matrix.map_apply]`. Distinguish the cases in `h : decide ((i : ℕ) < x.a) = x.ty v j`. Distinguish the cases in `hi : (i : ℕ) < x.a`. Establish `ht : x.ty v j = true` using `by rw [← h]; simp [hi]`. Simplify using `[hi, ht]`.

Establish `ht : x.ty v j = false` using `by rw [← h]; simp [hi]`. Simplify using `[hi, ht]`. Rewrite using `[x.w_blk v i j h]`. Simplify using the standard rewrite rules. Establish `hEwi : x.wiX X v * E = E' * x.wiX X v`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = x.wiX X v * (E * x.wX X v) * x.wiX X v := by simp only [Matrix.mul_assoc]`. Use `_ = x.wiX X v * (x.wX X v * E') * x.wiX X v := by rw [hEw]`. Use `_ = E' * x.wiX X v := by rw [← Matrix.mul_assoc (x.wiX X v), hwi, Matrix.one_mul]`. Establish `hEZ : E * Z = Z - Z * E`.

Use extensionality with `k l`. Simplify using `only [E, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]`. Establish `hk` using `hZ k l`. Distinguish the cases in `hkl : ((k : ℕ) < x.a ↔ (l : ℕ) < x.a)`. Establish `h0 : Z k l = 0` using `by simpa using hk.1 hkl`.

Simplify using `[h0]`. Distinguish the cases in `hka : (k : ℕ) < x.a`. Establish `hla : ¬ (l : ℕ) < x.a` using `fun h => hkl ⟨fun _ => h, fun _ => hka⟩`. Simplify using `[hka, hla]`. Establish `hla : (l : ℕ) < x.a`.

Assume the negation of the conclusion as `h`. Conclude with `hkl ⟨fun h' => absurd h' hka, fun h' => absurd h' h⟩`. Simplify using `[hka, hla]`. Establish `hM : E' * (x.wiX X v * Z * x.wX X v) = x.wiX X v * Z * x.wX X v - x.wiX X v * Z * x.wX X v * E'`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hEwi, Matrix.mul_assoc (x.wiX X v) E Z, hEZ, Matrix.mul_sub, Matrix.sub_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hEw]`. Establish `hii` using `congrFun (congrFun hM i) i`. Simplify using `only [E', Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply] at hii`. Distinguish the cases in `ht : x.ty v i`.

Simplify `hii` using `[ht]`. Simplify `hii.symm` using `[ht]`.
-/
private theorem selCard_diag {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (Z : Matrix (Fin n) (Fin n) X) (hZ : Z ∈ Od x.A X n x.a) (i : Fin n) :
    (x.wiX X v * Z * x.wX X v) i i = 0 := by
  let E : Matrix (Fin n) (Fin n) X := Matrix.diagonal fun k => if (k : ℕ) < x.a then 1 else 0
  let E' : Matrix (Fin n) (Fin n) X := Matrix.diagonal fun k => if x.ty v k then 1 else 0
  have hwi : x.wiX X v * x.wX X v = 1 := by
    simp only [NP.wiX, NP.wX]
    rw [← Matrix.map_mul, (x.w v).inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hw' : x.wX X v * x.wiX X v = 1 := by
    simp only [NP.wiX, NP.wX]
    rw [← Matrix.map_mul, (x.w v).mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hEw : E * x.wX X v = x.wX X v * E' := by
    ext i j
    simp only [E, E', Matrix.diagonal_mul, Matrix.mul_diagonal, NP.wX, Matrix.map_apply]
    by_cases h : decide ((i : ℕ) < x.a) = x.ty v j
    · by_cases hi : (i : ℕ) < x.a
      · have ht : x.ty v j = true := by rw [← h]; simp [hi]
        simp [hi, ht]
      · have ht : x.ty v j = false := by rw [← h]; simp [hi]
        simp [hi, ht]
    · rw [x.w_blk v i j h]
      simp
  have hEwi : x.wiX X v * E = E' * x.wiX X v := by
    calc x.wiX X v * E = x.wiX X v * E * (x.wX X v * x.wiX X v) := by rw [hw', Matrix.mul_one]
    _ = x.wiX X v * (E * x.wX X v) * x.wiX X v := by simp only [Matrix.mul_assoc]
    _ = x.wiX X v * (x.wX X v * E') * x.wiX X v := by rw [hEw]
    _ = E' * x.wiX X v := by rw [← Matrix.mul_assoc (x.wiX X v), hwi, Matrix.one_mul]
  have hEZ : E * Z = Z - Z * E := by
    ext k l
    simp only [E, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]
    have hk := hZ k l
    by_cases hkl : ((k : ℕ) < x.a ↔ (l : ℕ) < x.a)
    · have h0 : Z k l = 0 := by simpa using hk.1 hkl
      simp [h0]
    · by_cases hka : (k : ℕ) < x.a
      · have hla : ¬ (l : ℕ) < x.a := fun h => hkl ⟨fun _ => h, fun _ => hka⟩
        simp [hka, hla]
      · have hla : (l : ℕ) < x.a := by
          by_contra h
          exact hkl ⟨fun h' => absurd h' hka, fun h' => absurd h' h⟩
        simp [hka, hla]
  have hM : E' * (x.wiX X v * Z * x.wX X v) =
      x.wiX X v * Z * x.wX X v - x.wiX X v * Z * x.wX X v * E' := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hEwi, Matrix.mul_assoc (x.wiX X v) E Z, hEZ,
      Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    rw [hEw]
  have hii := congrFun (congrFun hM i) i
  simp only [E', Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply] at hii
  by_cases ht : x.ty v i
  · simpa [ht] using hii
  · simpa [ht] using hii.symm

/- English proof (translation)
Use `y.2.2 1 1` as an intermediate fact. Simplify using `using this`.
-/
private theorem selCard_one {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] (M : FRep A Γ) (y : Z1 M.ρ) :
    y.1 1 = 0 := by
  have := y.2.2 1 1
  simpa using this

private def selCard_d {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] (M : FRep A Γ) (m : M.X) : Z1 M.ρ :=
  ⟨fun g => M.ρ g m - m,
    (continuous_of_discreteTopology (f := fun z : M.X => z - m)).comp
      (M.cont.comp (continuous_id.prodMk continuous_const)),
    fun g h => by simp [map_sub]⟩

/- English proof (translation)
Apply `(Submodule.Quotient.eq _).2` to reduce the goal to its premises. Use `show ((y + selCard_d M m - y : Z1 M.ρ) : _ → M.X) ∈ B1 M.ρ`. Rewrite using `[add_sub_cancel_left, mem_coboundaries1]`. Conclude with `⟨m, fun g => rfl⟩`.
-/
private theorem selCard_mk {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] (M : FRep A Γ) (y : Z1 M.ρ)
    (m : M.X) : (Submodule.Quotient.mk (y + selCard_d M m) : H1 M.ρ) = Submodule.Quotient.mk y := by
  apply (Submodule.Quotient.eq _).2
  show ((y + selCard_d M m - y : Z1 M.ρ) : _ → M.X) ∈ B1 M.ρ
  rw [add_sub_cancel_left, mem_coboundaries1]
  exact ⟨m, fun g => rfl⟩

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ s`. Establish `hcc : M.ρ c (y.1 c) = -y.1 c`. Establish `h` using `y.2.2 c c`. Rewrite `h` using `[hc, selCard_one M y]`. Conclude with `(eq_neg_of_add_eq_zero_right h.symm)`.

Use `⟨y + selCard_d M (((h2.unit⁻¹ : Aˣ) : A) • y.1 c), ?_, selCard_mk M y _⟩` and prove the remaining obligations. Use `show y.1 c + (M.ρ c (((h2.unit⁻¹ : Aˣ) : A) • y.1 c) - ((h2.unit⁻¹ : Aˣ) : A) • y.1 c) = 0`. Rewrite using `[map_smul, hcc]`. Establish `h2u : ((h2.unit⁻¹ : Aˣ) : A) * 2 = 1` using `by simp`. Establish `hsplit : (((h2.unit⁻¹ : Aˣ) : A) * 2) • y.1 c = ((h2.unit⁻¹ : Aˣ) : A) • y.1 c + ((h2.unit⁻¹ : Aˣ) : A) • y.1 c`.

Rewrite using `[mul_two, add_smul]`. Rewrite `hsplit` using `[h2u, one_smul]`. Rewrite using `[smul_neg]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem selCard_norm {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] (M : FRep A Γ)
    (h2 : IsUnit (2 : A)) (c : Γ) (hc : c * c = 1) (s : H1 M.ρ) :
    ∃ y : Z1 M.ρ, y.1 c = 0 ∧ Submodule.Quotient.mk y = s := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  have hcc : M.ρ c (y.1 c) = -y.1 c := by
    have h := y.2.2 c c
    rw [hc, selCard_one M y] at h
    exact (eq_neg_of_add_eq_zero_right h.symm)
  refine ⟨y + selCard_d M (((h2.unit⁻¹ : Aˣ) : A) • y.1 c), ?_, selCard_mk M y _⟩
  show y.1 c + (M.ρ c (((h2.unit⁻¹ : Aˣ) : A) • y.1 c) - ((h2.unit⁻¹ : Aˣ) : A) • y.1 c) = 0
  rw [map_smul, hcc]
  have h2u : ((h2.unit⁻¹ : Aˣ) : A) * 2 = 1 := by simp
  have hsplit : (((h2.unit⁻¹ : Aˣ) : A) * 2) • y.1 c =
      ((h2.unit⁻¹ : Aˣ) : A) • y.1 c + ((h2.unit⁻¹ : Aˣ) : A) • y.1 c := by
    rw [mul_two, add_smul]
  rw [h2u, one_smul] at hsplit
  rw [smul_neg]
  calc y.1 c + (-(((h2.unit⁻¹ : Aˣ) : A) • y.1 c) - ((h2.unit⁻¹ : Aˣ) : A) • y.1 c)
      = y.1 c - (((h2.unit⁻¹ : Aˣ) : A) • y.1 c + ((h2.unit⁻¹ : Aˣ) : A) • y.1 c) := by abel
    _ = 0 := by rw [← hsplit, sub_self]

/- English proof (translation)
Establish `hc2 : ∀ z : Z1 M.ρ, z.1 G.c = 0 → ∀ g, z.1 (g * G.c) = z.1 g`. Introduce `z hz g`. Rewrite using `[z.2.2, hz, map_zero, add_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Break down `Int.units_eq_one_or (G.η g) with hg | hg` into its components or cases. Conclude with `H ⟨g, hg⟩`. Establish `hk : G.η (g * G.c) = 1` using `by rw [map_mul, hg, G.η_c]; rfl`. Rewrite using `[← hc2 y h g, ← hc2 y' h' g]`. Conclude with `H ⟨g * G.c, hk⟩`.
-/
private theorem selCard_inj {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L) {A : Type} [CommRing A] (M : FRep A G.Γ)
    (y y' : Z1 M.ρ) (h : y.1 G.c = 0) (h' : y'.1 G.c = 0) (H : ∀ g : G.G₀, y.1 g = y'.1 g) : y = y' := by
  have hc2 : ∀ z : Z1 M.ρ, z.1 G.c = 0 → ∀ g, z.1 (g * G.c) = z.1 g := by
    intro z hz g
    rw [z.2.2, hz, map_zero, add_zero]
  apply Subtype.ext
  funext g
  rcases Int.units_eq_one_or (G.η g) with hg | hg
  · exact H ⟨g, hg⟩
  · have hk : G.η (g * G.c) = 1 := by rw [map_mul, hg, G.η_c]; rfl
    rw [← hc2 y h g, ← hc2 y' h' g]
    exact H ⟨g * G.c, hk⟩

/- English proof (translation)
Establish `h1` using `(Submodule.mem_iInf _).1 hy w`. Simplify using `only [Submodule.mem_comap, H1ur, LinearMap.mem_ker, Dat.loc1, pairH1DecompositionMap, resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.coe_subtype, mem_coboundaries1] at h1`. Take `⟨q, hq⟩` from `h1`. Take `⟨m, rfl⟩` from `D.surj w q`. Use `⟨m, fun g hg => ?_⟩` and prove the remaining obligations.

Establish `e2 : D.π w (y.1 (P.φ w g)) = (D.Q w).ρ g (D.π w m) - D.π w m` using `hq ⟨g, hg⟩`. Use `⟨e2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, D.equiv, e2, sub_self]`.
-/
private theorem selCard_loc {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (y : Z1 D.M.ρ) (hy : (Submodule.Quotient.mk y : H1 D.M.ρ) ∈ D.Sel) (w : P.ι) :
    ∃ m : D.M.X, ∀ g ∈ P.J w, D.π w (y.1 (P.φ w g)) = (D.Q w).ρ g (D.π w m) - D.π w m ∧
      D.π w (y.1 (P.φ w g) - (D.M.ρ (P.φ w g) m - m)) = 0 := by
  have h1 := (Submodule.mem_iInf _).1 hy w
  simp only [Submodule.mem_comap, H1ur, LinearMap.mem_ker, Dat.loc1, pairH1DecompositionMap, resH1, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.coe_subtype, mem_coboundaries1] at h1
  obtain ⟨q, hq⟩ := h1
  obtain ⟨m, rfl⟩ := D.surj w q
  refine ⟨m, fun g hg => ?_⟩
  have e2 : D.π w (y.1 (P.φ w g)) = (D.Q w).ρ g (D.π w m) - D.π w m := hq ⟨g, hg⟩
  refine ⟨e2, ?_⟩
  rw [map_sub, map_sub, D.equiv, e2, sub_self]

/- English proof (translation)
Establish `hl : ∀ m1 m2 : D.M.X, ((o.e (m1 - m2) : Matrix (Fin n) (Fin n) (x.Am e))) = (o.e m1 : Matrix (Fin n) (Fin n) (x.Am e)) - o.e m2` using `fun m1 m2 => by`. Rewrite using `[map_sub, Submodule.coe_sub]`. Establish `ha : ∀ m1 m2 : D.M.X, ((o.e (m1 + m2) : Matrix (Fin n) (Fin n) (x.Am e))) = (o.e m1 : Matrix (Fin n) (Fin n) (x.Am e)) + o.e m2` using `fun m1 m2 => by`. Rewrite using `[map_add, Submodule.coe_add]`. Establish `hcoc : ∀ a b : G.Γ, y.1 (a * b) = y.1 a + D.M.ρ a (y.1 b)` using `y.2.2`.

Establish `hcinv : G.c⁻¹ = G.c` using `inv_eq_of_mul_eq_one_right G.c_sq`. Use `⟨fun g => (o.e _).2, fun i j => ?_, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, -, -, ht, -⟩` from `finAm l G0.frame n x e 0`. Rewrite using `[adicLC _ _ _ e _ ht]`. Establish `hyc : IsLocallyConstant y.1` using `(IsLocallyConstant.iff_continuous _).2 y.2.1`.

Conclude with `(hyc.comp_continuous continuous_subtype_val).comp fun m => (o.e m : Matrix (Fin n) (Fin n) (x.Am e)) i j`. Use `show (o.e (y.1 ((g * g' : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) = o.e (y.1 g) + x.ρX (x.Am e) (h.p₀ g) * o.e (y.1 g') * x.ρX (x.Am e) (h.p₀ g⁻¹)`. Rewrite using `[Subgroup.coe_mul, hcoc, ha, o.act]`. Use `show (o.e (y.1 ((G.frame.conj g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) = -(o.e (y.1 g) : Matrix (Fin n) (Fin n) (x.Am e))ᵀ`. Establish `hcj : ((G.frame.conj g : G.frame.G₀) : G.Γ) = G.c * (g : G.Γ) * G.c⁻¹` using `rfl`.

Rewrite using `[hcj, hcoc, hcoc, hcinv, hc, map_zero, add_zero, zero_add, o.actc]`. Take `⟨g', hg', rfl⟩` from `Subgroup.mem_map.1 hg`. Take `⟨m, hm⟩` from `selCard_loc D y hy (Sum.inr u)`. Establish `h0` using `(hm g' hg').1`. Establish `hk` using `(odKill l L G G0 h n x (x.Am e) D o).2.2 u g' hg' (D.π (Sum.inr u) m)`.

Establish `hz : y.1 ((plOf G).φ (Sum.inr u) g') = 0`. Apply `o.kerU u` to reduce the goal to its premises. Rewrite using `[map_zero, h0]`. Conclude with `sub_eq_zero.2 hk`. Use `show (o.e (y.1 ((plOf G).φ (Sum.inr u) g')) : Matrix (Fin n) (Fin n) (x.Am e)) = 0`.

Rewrite using `[hz, map_zero, Submodule.coe_zero]`. Take `⟨m, hm⟩` from `selCard_loc D y hy (Sum.inl v)`. Use `⟨o.e m, (o.e m).2, fun g => ⟨fun i j hij => ?_, fun _ i => ?_⟩⟩` and prove the remaining obligations. Establish `hE : ((o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) : Matrix (Fin n) (Fin n) (x.Am e))) = (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) - dY G.frame (fun g => x.ρX (x.Am e) (h.p₀ g)) (o.e m) (G.φ v g)`. Rewrite using `[hl, hl, o.act]`.

Both sides reduce to the same expression. Establish `hk : (x.wiX (x.Am e) v * (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) : Matrix (Fin n) (Fin n) (x.Am e)) * x.wX (x.Am e) v) i j = 0` using `(o.kerV v _).1 (hm g (Subgroup.mem_top g)).2 i j hij`. Rewrite `hk` using `[hE]`. Conclude with `hk`. Establish `hE : ((o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) : Matrix (Fin n) (Fin n) (x.Am e))) = (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) - dY G.frame (fun g => x.ρX (x.Am e) (h.p₀ g)) (o.e m) (G.φ v g)`.

Rewrite using `[hl, hl, o.act]`. Both sides reduce to the same expression. Establish `hk` using `selCard_diag x (x.Am e) v _ (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m))).2 i`. Rewrite `hk` using `[hE]`. Conclude with `hk`.
-/
private theorem selCard_mem {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ}
    {x : NP G0.frame n} {e : ℕ} {D : Dat x.A (plOf G)} (o : IsOd h x (x.Am e) D) (y : Z1 D.M.ρ) (hc : y.1 G.c = 0)
    (hy : (Submodule.Quotient.mk y : H1 D.M.ρ) ∈ D.Sel) :
    (fun g : G.G₀ => (o.e (y.1 g) : Matrix (Fin n) (Fin n) (x.Am e))) ∈ SelM h x (x.Am e) := by
  have hl : ∀ m1 m2 : D.M.X, ((o.e (m1 - m2) : Matrix (Fin n) (Fin n) (x.Am e))) =
      (o.e m1 : Matrix (Fin n) (Fin n) (x.Am e)) - o.e m2 := fun m1 m2 => by
    rw [map_sub, Submodule.coe_sub]
  have ha : ∀ m1 m2 : D.M.X, ((o.e (m1 + m2) : Matrix (Fin n) (Fin n) (x.Am e))) =
      (o.e m1 : Matrix (Fin n) (Fin n) (x.Am e)) + o.e m2 := fun m1 m2 => by
    rw [map_add, Submodule.coe_add]
  have hcoc : ∀ a b : G.Γ, y.1 (a * b) = y.1 a + D.M.ρ a (y.1 b) := y.2.2
  have hcinv : G.c⁻¹ = G.c := inv_eq_of_mul_eq_one_right G.c_sq
  refine ⟨fun g => (o.e _).2, fun i j => ?_, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
  · obtain ⟨-, -, -, -, -, ht, -⟩ := finAm l G0.frame n x e 0
    rw [adicLC _ _ _ e _ ht]
    have hyc : IsLocallyConstant y.1 := (IsLocallyConstant.iff_continuous _).2 y.2.1
    exact (hyc.comp_continuous continuous_subtype_val).comp
      fun m => (o.e m : Matrix (Fin n) (Fin n) (x.Am e)) i j
  · show (o.e (y.1 ((g * g' : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) =
      o.e (y.1 g) + x.ρX (x.Am e) (h.p₀ g) * o.e (y.1 g') * x.ρX (x.Am e) (h.p₀ g⁻¹)
    rw [Subgroup.coe_mul, hcoc, ha, o.act]
  · show (o.e (y.1 ((G.frame.conj g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) =
      -(o.e (y.1 g) : Matrix (Fin n) (Fin n) (x.Am e))ᵀ
    have hcj : ((G.frame.conj g : G.frame.G₀) : G.Γ) = G.c * (g : G.Γ) * G.c⁻¹ := rfl
    rw [hcj, hcoc, hcoc, hcinv, hc, map_zero, add_zero, zero_add, o.actc]
  · obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨m, hm⟩ := selCard_loc D y hy (Sum.inr u)
    have h0 := (hm g' hg').1
    have hk := (odKill l L G G0 h n x (x.Am e) D o).2.2 u g' hg' (D.π (Sum.inr u) m)
    have hz : y.1 ((plOf G).φ (Sum.inr u) g') = 0 := by
      apply o.kerU u
      rw [map_zero, h0]
      exact sub_eq_zero.2 hk
    show (o.e (y.1 ((plOf G).φ (Sum.inr u) g')) : Matrix (Fin n) (Fin n) (x.Am e)) = 0
    rw [hz, map_zero, Submodule.coe_zero]
  · obtain ⟨m, hm⟩ := selCard_loc D y hy (Sum.inl v)
    refine ⟨o.e m, (o.e m).2, fun g => ⟨fun i j hij => ?_, fun _ i => ?_⟩⟩
    · have hE : ((o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) :
            Matrix (Fin n) (Fin n) (x.Am e))) =
          (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) -
            dY G.frame (fun g => x.ρX (x.Am e) (h.p₀ g)) (o.e m) (G.φ v g) := by
        rw [hl, hl, o.act]
        rfl
      have hk : (x.wiX (x.Am e) v * (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) -
          (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) : Matrix (Fin n) (Fin n) (x.Am e)) *
            x.wX (x.Am e) v) i j = 0 :=
        (o.kerV v _).1 (hm g (Subgroup.mem_top g)).2 i j hij
      rw [hE] at hk
      exact hk
    · have hE : ((o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m)) :
            Matrix (Fin n) (Fin n) (x.Am e))) =
          (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) -
            dY G.frame (fun g => x.ρX (x.Am e) (h.p₀ g)) (o.e m) (G.φ v g) := by
        rw [hl, hl, o.act]
        rfl
      have hk := selCard_diag x (x.Am e) v _
        (o.e (y.1 ((G.φ v g : G.frame.G₀) : G.Γ) - (D.M.ρ ((G.φ v g : G.frame.G₀) : G.Γ) m - m))).2 i
      rw [hE] at hk
      exact hk

/- English proof (translation)
Introduce `l _ L G G0 h n x e D hl o hfin`. Establish `h2 : IsUnit (2 : x.A)` using `(finAm l G0.frame n x e 0).2.2.2.2.2.2.2.1 hl`. Establish `ys : ∀ s : D.Sel, ∃ y : Z1 D.M.ρ, y.1 G.c = 0 ∧ Submodule.Quotient.mk y = (s : H1 D.M.ρ)` using `fun s => selCard_norm D.M h2 G.c G.c_sq s`. Use `choose Ys hYc hYs using ys`. Establish `bd : ∀ b : BdM h x (x.Am e), ∃ m : D.M.X, D.M.ρ G.c m = m ∧ b.1 = fun g : G.frame.G₀ => (o.e ((selCard_d D.M m).1 (g : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e))`.

Introduce and unpack `⟨b, Y, hY, hYt, rfl⟩`. Use `⟨o.e.symm ⟨Y, hY⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `o.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[o.actc, LinearEquiv.apply_symm_apply]`.

Use `show -Yᵀ = Y`. Rewrite using `[hYt, neg_neg]`. Use function extensionality and compare the values at `g`. Establish `hd : (selCard_d D.M (o.e.symm ⟨Y, hY⟩)).1 (g : G.Γ) = D.M.ρ (g : G.Γ) (o.e.symm ⟨Y, hY⟩) - o.e.symm ⟨Y, hY⟩` using `rfl`. Rewrite using `[hd, map_sub, Submodule.coe_sub, o.act, LinearEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Use `choose mb hmbc hmb using bd`. Establish `hz : ∀ (s : D.Sel) (b : BdM h x (x.Am e)), (Ys s + selCard_d D.M (mb b)).1 G.c = 0`. Introduce `s b`. Use `show (Ys s).1 G.c + (D.M.ρ G.c (mb b) - mb b) = 0`.

Rewrite using `[hmbc, sub_self, add_zero, hYc]`. Establish `hS : ∀ s b, (Submodule.Quotient.mk (Ys s + selCard_d D.M (mb b)) : H1 D.M.ρ) ∈ D.Sel`. Introduce `s b`. Rewrite using `[selCard_mk, hYs]`. Conclude with `s.2`.

Set `Φ : D.Sel × BdM h x (x.Am e) → SelM h x (x.Am e)` to `fun p => ⟨_, selCard_mem o _ (hz p.1 p.2) (hS p.1 p.2)⟩`. Establish `hinj : Function.Injective Φ`. Introduce and unpack `⟨s, b⟩ ⟨s', b'⟩ hp`. Establish `hv` using `congrArg Subtype.val hp`. Establish `heq : Ys s + selCard_d D.M (mb b) = Ys s' + selCard_d D.M (mb b')`.

Apply `selCard_inj G D.M _ _ (hz s b) (hz s' b')` to reduce the goal to its premises. Introduce `g`. Establish `hg` using `congrFun hv g`. Conclude with `o.e.injective (Subtype.ext hg)`. Establish `hss : s = s'`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hYs s, ← hYs s', ← selCard_mk D.M (Ys s) (mb b), ← selCard_mk D.M (Ys s') (mb b'), heq]`. Substitute `hss` using the available equality. Establish `hdd : selCard_d D.M (mb b) = selCard_d D.M (mb b')` using `add_left_cancel heq`. Establish `hbb : b = b'`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hmb b, hmb b', hdd]`. Rewrite using `[hbb]`. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod]`. Use `haveI := hfin.to_subtype`.

Conclude with `Nat.card_le_card_of_injective Φ hinj`.
-/
theorem UpperTheory.card_selmer_mul_card_boundary_le_card_selmerMatrix :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (e : ℕ) (D : Dat x.A (plOf G)), l ≠ 2 → IsOd h x (x.Am e) D → (SelM h x (x.Am e)).Finite → Nat.card D.Sel * (BdM h x (x.Am e)).ncard ≤ (SelM h x (x.Am e)).ncard := by
  intro l _ L G G0 h n x e D hl o hfin
  classical
  have h2 : IsUnit (2 : x.A) := (finAm l G0.frame n x e 0).2.2.2.2.2.2.2.1 hl
  have ys : ∀ s : D.Sel, ∃ y : Z1 D.M.ρ, y.1 G.c = 0 ∧ Submodule.Quotient.mk y = (s : H1 D.M.ρ) :=
    fun s => selCard_norm D.M h2 G.c G.c_sq s
  choose Ys hYc hYs using ys
  have bd : ∀ b : BdM h x (x.Am e), ∃ m : D.M.X, D.M.ρ G.c m = m ∧
      b.1 = fun g : G.frame.G₀ => (o.e ((selCard_d D.M m).1 (g : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)) := by
    rintro ⟨b, Y, hY, hYt, rfl⟩
    refine ⟨o.e.symm ⟨Y, hY⟩, ?_, ?_⟩
    · apply o.e.injective
      apply Subtype.ext
      rw [o.actc, LinearEquiv.apply_symm_apply]
      show -Yᵀ = Y
      rw [hYt, neg_neg]
    · funext g
      have hd : (selCard_d D.M (o.e.symm ⟨Y, hY⟩)).1 (g : G.Γ) =
          D.M.ρ (g : G.Γ) (o.e.symm ⟨Y, hY⟩) - o.e.symm ⟨Y, hY⟩ := rfl
      rw [hd, map_sub, Submodule.coe_sub, o.act, LinearEquiv.apply_symm_apply]
      rfl
  choose mb hmbc hmb using bd
  have hz : ∀ (s : D.Sel) (b : BdM h x (x.Am e)), (Ys s + selCard_d D.M (mb b)).1 G.c = 0 := by
    intro s b
    show (Ys s).1 G.c + (D.M.ρ G.c (mb b) - mb b) = 0
    rw [hmbc, sub_self, add_zero, hYc]
  have hS : ∀ s b, (Submodule.Quotient.mk (Ys s + selCard_d D.M (mb b)) : H1 D.M.ρ) ∈ D.Sel := by
    intro s b
    rw [selCard_mk, hYs]
    exact s.2
  let Φ : D.Sel × BdM h x (x.Am e) → SelM h x (x.Am e) := fun p =>
    ⟨_, selCard_mem o _ (hz p.1 p.2) (hS p.1 p.2)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨s, b⟩ ⟨s', b'⟩ hp
    have hv := congrArg Subtype.val hp
    have heq : Ys s + selCard_d D.M (mb b) = Ys s' + selCard_d D.M (mb b') := by
      apply selCard_inj G D.M _ _ (hz s b) (hz s' b')
      intro g
      have hg := congrFun hv g
      exact o.e.injective (Subtype.ext hg)
    have hss : s = s' := by
      apply Subtype.ext
      rw [← hYs s, ← hYs s', ← selCard_mk D.M (Ys s) (mb b), ← selCard_mk D.M (Ys s') (mb b'), heq]
    subst hss
    have hdd : selCard_d D.M (mb b) = selCard_d D.M (mb b') := add_left_cancel heq
    have hbb : b = b' := by
      apply Subtype.ext
      rw [hmb b, hmb b', hdd]
    rw [hbb]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod]
  haveI := hfin.to_subtype
  exact Nat.card_le_card_of_injective Φ hinj
