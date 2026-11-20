import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Establish `key : ∀ (p q : x.A) (y : Y), u (algebraMap x.A Y p * y * algebraMap x.A Y q) = algebraMap x.A Z p * u y * algebraMap x.A Z q`. Introduce `p q y`. Establish `h1 : algebraMap x.A Y p * y * algebraMap x.A Y q = (p * q) • y`. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : algebraMap x.A Z p * u y * algebraMap x.A Z q = (p * q) • u y`. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2, map_smul]`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => key _ _ _`.
-/
private theorem map_algebraMap_mul_mul_map_linearMap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (P Q : Matrix (Fin n) (Fin n) x.A) (N : Matrix (Fin n) (Fin n) Y) :
    (P.map (algebraMap x.A Y) * N * Q.map (algebraMap x.A Y)).map u = P.map (algebraMap x.A Z) * N.map u * Q.map (algebraMap x.A Z) := by
  have key : ∀ (p q : x.A) (y : Y), u (algebraMap x.A Y p * y * algebraMap x.A Y q) = algebraMap x.A Z p * u y * algebraMap x.A Z q := by
    intro p q y
    have h1 : algebraMap x.A Y p * y * algebraMap x.A Y q = (p * q) • y := by
      rw [Algebra.smul_def, map_mul]; ring
    have h2 : algebraMap x.A Z p * u y * algebraMap x.A Z q = (p * q) • u y := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [h1, h2, map_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => key _ _ _

/- English proof (translation)
Use `⟨Matrix.of fun i j => if h : S i j then 0 else (hr i j h).choose, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `[hij]`. Use extensionality with `i j`. Distinguish the cases in `hij : S i j`.

Simplify using `[hij, h0 i j hij]`. Simplify using `[hij, (hr i j hij).choose_spec]`.
-/
private theorem exists_matrix_map_eq_of_zero_on_of_mem_range {n : ℕ} {R Y Z : Type} [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (w : Y →ₗ[R] Z) (S : Fin n → Fin n → Prop) (N : Matrix (Fin n) (Fin n) Z) (h0 : ∀ i j, S i j → N i j = 0) (hr : ∀ i j, ¬ S i j → N i j ∈ Set.range w) :
    ∃ N' : Matrix (Fin n) (Fin n) Y, (∀ i j, S i j → N' i j = 0) ∧ N'.map w = N := by
  classical
  refine ⟨Matrix.of fun i j => if h : S i j then 0 else (hr i j h).choose, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · ext i j
    by_cases hij : S i j
    · simp [hij, h0 i j hij]
    · simp [hij, (hr i j hij).choose_spec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hN i j hij`. Conclude with `(Submodule.mem_bot _).1 ((hN i j).1 hij)`. Introduce `hN i j`. Conclude with `⟨fun hij => (Submodule.mem_bot _).2 (hN i j hij), fun _ => Submodule.mem_top⟩`.
-/
private theorem mem_od_iff_entry_eq_zero_of_same_block {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} (N : Matrix (Fin n) (Fin n) R) :
    N ∈ Od A R n a ↔ ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → N i j = 0 := by
  constructor
  · intro hN i j hij
    exact (Submodule.mem_bot _).1 ((hN i j).1 hij)
  · intro hN i j
    exact ⟨fun hij => (Submodule.mem_bot _).2 (hN i j hij), fun _ => Submodule.mem_top⟩

/- English proof (translation)
Use `set W : Matrix (Fin n) (Fin n) (PowerSeries x.K) := ((x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hW`. Use `set B : Matrix (Fin n) (Fin n) (PowerSeries x.K) := (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hB`. Establish `hBW : B * W = 1` using `Units.inv_mul (x.w v)`. Establish `hWB : W * B = 1` using `Units.mul_inv (x.w v)`. Set `β : Bool → PowerSeries x.K` to `fun b => if b then 1 else 0`.

Establish `hpat : W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) = Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * W`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : decide ((i : ℕ) < x.a) = x.ty v j`. Rewrite using `[h]`.

Put the polynomial expressions in normal form. Rewrite using `[show W i j = 0 from x.w_blk v i j h]`. Simplify using the standard rewrite rules. Establish `key : Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a)))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hBW, Matrix.one_mul]`. Use `_ = B * (W * Matrix.diagonal (fun j : Fin n => β (x.ty v j))) * B := by rw [Matrix.mul_assoc B]`. Use `_ = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * (W * B) := by`. Rewrite using `[hpat]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hWB, Matrix.mul_one]`. Establish `e` using `congrArg (fun M : Matrix (Fin n) (Fin n) (PowerSeries x.K) => M j k) key`. Simplify using `only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e`. Express the relevant statement in the definitionally equal form `B j k = 0`. Apply the tactic sequence `cases h1 : x.ty v j <;> cases h2 : decide ((k : ℕ) < x.a) <;> simp only [h1, h2, β] at e hjk <;> simp_all`.
-/
private theorem inv_w_entry_eq_zero_of_ty_ne_lt_a {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (j k : Fin n) (hjk : x.ty v j ≠ decide ((k : ℕ) < x.a)) :
    (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) j k = 0 := by
  classical
  set W : Matrix (Fin n) (Fin n) (PowerSeries x.K) := ((x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hW
  set B : Matrix (Fin n) (Fin n) (PowerSeries x.K) := (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hB
  have hBW : B * W = 1 := Units.inv_mul (x.w v)
  have hWB : W * B = 1 := Units.mul_inv (x.w v)
  let β : Bool → PowerSeries x.K := fun b => if b then 1 else 0
  have hpat : W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) = Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * W := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : decide ((i : ℕ) < x.a) = x.ty v j
    · rw [h]; ring_nf
    · rw [show W i j = 0 from x.w_blk v i j h]; simp
  have key : Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) := by
    calc Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B := by
          rw [hBW, Matrix.one_mul]
      _ = B * (W * Matrix.diagonal (fun j : Fin n => β (x.ty v j))) * B := by rw [Matrix.mul_assoc B]
      _ = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * (W * B) := by
          rw [hpat]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWB, Matrix.mul_one]
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (PowerSeries x.K) => M j k) key
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  change B j k = 0
  cases h1 : x.ty v j <;> cases h2 : decide ((k : ℕ) < x.a) <;> simp only [h1, h2, β] at e hjk <;> simp_all

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : x.ty v i = decide ((k : ℕ) < x.a)`.

Distinguish the cases in `h2 : decide ((l : ℕ) < x.a) = x.ty v j`. Rewrite using `[hN k l (decide_eq_decide.mp (by rw [← h1, hij, ← h2]))]; simp`. Simplify using `[NP.wX, x.w_blk v l j h2]`. Simplify using `only [NP.wiX, Matrix.map_apply]`. Rewrite using `[inv_w_entry_eq_zero_of_ty_ne_lt_a x v i k h1]`.

Simplify using the standard rewrite rules.
-/
private theorem wiX_mul_mul_wX_eq_zero_of_ty_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (N : Matrix (Fin n) (Fin n) Y) (hN : ∀ k l : Fin n, ((k : ℕ) < x.a ↔ (l : ℕ) < x.a) → N k l = 0) (i j : Fin n) (hij : x.ty v i = x.ty v j) :
    (x.wiX Y v * N * x.wX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : x.ty v i = decide ((k : ℕ) < x.a)
  · by_cases h2 : decide ((l : ℕ) < x.a) = x.ty v j
    · rw [hN k l (decide_eq_decide.mp (by rw [← h1, hij, ← h2]))]; simp
    · simp [NP.wX, x.w_blk v l j h2]
  · simp only [NP.wiX, Matrix.map_apply]
    rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v i k h1]; simp

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : decide ((i : ℕ) < x.a) = x.ty v k`.

Distinguish the cases in `h2 : x.ty v l = decide ((j : ℕ) < x.a)`. Rewrite using `[hP k l (by rw [← h1, h2]; exact decide_eq_decide.mpr hij)]; simp`. Simplify using `only [NP.wiX, Matrix.map_apply]`. Rewrite using `[inv_w_entry_eq_zero_of_ty_ne_lt_a x v l j h2]`. Simplify using the standard rewrite rules.

Simplify using `[NP.wX, x.w_blk v i k h1]`.
-/
private theorem wX_mul_mul_wiX_eq_zero_of_same_block {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (P : Matrix (Fin n) (Fin n) Y) (hP : ∀ k l : Fin n, x.ty v k = x.ty v l → P k l = 0) (i j : Fin n) (hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) :
    (x.wX Y v * P * x.wiX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : decide ((i : ℕ) < x.a) = x.ty v k
  · by_cases h2 : x.ty v l = decide ((j : ℕ) < x.a)
    · rw [hP k l (by rw [← h1, h2]; exact decide_eq_decide.mpr hij)]; simp
    · simp only [NP.wiX, Matrix.map_apply]
      rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v l j h2]; simp
  · simp [NP.wX, x.w_blk v i k h1]

/- English proof (translation)
Unfold `NP.wX NP.wiX`. Conclude with `⟨map_algebraMap_mul_mul_map_linearMap x u _ _ N, map_algebraMap_mul_mul_map_linearMap x u _ _ N⟩`.
-/
private theorem map_wiX_mul_mul_wX_and_wX_mul_mul_wiX {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (N : Matrix (Fin n) (Fin n) Y) :
    (x.wiX Y v * N * x.wX Y v).map u = x.wiX Z v * N.map u * x.wX Z v ∧
      (x.wX Y v * N * x.wiX Y v).map u = x.wX Z v * N.map u * x.wiX Z v := by
  unfold NP.wX NP.wiX
  exact ⟨map_algebraMap_mul_mul_map_linearMap x u _ _ N, map_algebraMap_mul_mul_map_linearMap x u _ _ N⟩

/- English proof (translation)
Unfold `NP.wX NP.wiX`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Matrix.map_mul, Units.inv_mul]`. Simplify using the standard rewrite rules. Rewrite using `[← Matrix.map_mul, Units.mul_inv]`.

Simplify using the standard rewrite rules.
-/
private theorem wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] :
    x.wiX Y v * x.wX Y v = 1 ∧ x.wX Y v * x.wiX Y v = 1 := by
  unfold NP.wX NP.wiX
  constructor
  · rw [← Matrix.map_mul, Units.inv_mul]; simp
  · rw [← Matrix.map_mul, Units.mul_inv]; simp

/- English proof (translation)
Introduce `l _ L G G0 h n x X' _ _ X _ _ X'' _ _ D' D D'' o' o o'' u v f g hf hg hu hex hv`. Establish `inj : Function.Injective f.f`. Introduce `m1 m2 h12`. Apply `o'.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e1` using `hf m1`. Rewrite `e1` using `[h12, hf m2]`. Use extensionality with `i j`. Conclude with `hu (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X => M i j) e1.symm)`. Establish `ex : Function.Exact f.f g.f`.

Introduce `m`. Prove the components needed by the constructor for the conclusion. Introduce `hgm`. Establish `h0 : (↑(o.e m) : Matrix (Fin n) (Fin n) X).map v = 0`. Rewrite using `[← hg m, hgm]`.

Simplify using the standard rewrite rules. Take `⟨N', hN'0, hN'⟩` from `exists_matrix_map_eq_of_zero_on_of_mem_range u (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o.e m)) (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o.e m).2 i j hij) (fun i j _ => (hex _).1 (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X'' => M …`. Use `⟨o'.e.symm ⟨N', (mem_od_iff_entry_eq_zero_of_same_block _).2 hN'0⟩, ?_⟩` and prove the remaining obligations. Apply `o.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hf, LinearEquiv.apply_symm_apply]`. Conclude with `hN'`. Introduce and unpack `⟨m', rfl⟩`. Apply `o''.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hg, hf, map_zero]`. Use extensionality with `i j`. Simplify using `using (hex _).2 ⟨_, rfl⟩`. Establish `surj : Function.Surjective g.f`. Introduce `m''`.

Take `⟨N, hN0, hN⟩` from `exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o''.e m'')) (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e m'').2 i j hij) (fun i j _ => hv _)`. Use `⟨o.e.symm ⟨N, (mem_od_iff_entry_eq_zero_of_same_block _).2 hN0⟩, ?_⟩` and prove the remaining obligations. Apply `o''.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hg, LinearEquiv.apply_symm_apply]`.

Conclude with `hN`. Use `⟨inj, ex, surj, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `q hq`.

Take `⟨m, rfl⟩` from `D'.surj w q`. Rewrite `hq` using `[f.comm]`. Break down `w with w | w` into its components or cases. Rewrite using `[o'.kerV]`. Rewrite `hq` using `[o.kerV]`.

Introduce `i j hji`. Establish `e` using `hq i j hji`. Rewrite `e` using `[hf, ← (map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w u _).1, Matrix.map_apply]`. Conclude with `hu (by rw [map_zero]; exact e)`. Establish `h1 : f.f m = 0` using `o.kerU w (by rw [hq, map_zero])`.

Rewrite using `[inj (h1.trans (map_zero f.f).symm), map_zero]`. Introduce `w q`. Prove the components needed by the constructor for the conclusion. Introduce `hq`. Take `⟨m, rfl⟩` from `D.surj w q`.

Rewrite `hq` using `[g.comm]`. Break down `w with w | w` into its components or cases. Establish `hlow` using `(o''.kerV w (g.f m)).1 hq`. Take `⟨P, hP0, hP⟩` from `exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => j < i ∨ x.ty w i = x.ty w j) (x.wiX X'' w * (↑(o''.e (g.f m)) : Matrix (Fin n) (Fin n) X'') * x.wX X'' w) (fun i j hij => hij.elim (hlow i j) (wiX_mul_mul_wX_eq_zero_of_ty_eq x w _ ((mem_od_iff_entry_eq_zero_of_sa …`. Establish `hN : x.wX X w * P * x.wiX X w ∈ Od x.A X n x.a` using `(mem_od_iff_entry_eq_zero_of_same_block _).2 (fun i j hij => wX_mul_mul_wiX_eq_zero_of_same_block x w P (fun k l hkl => hP0 k l (Or.inr hkl)) i j hij)`.

Take `⟨h1, h2⟩` from `wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X)`. Take `⟨h1'', h2''⟩` from `wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X'')`. Establish `hconj : x.wiX X w * (↑(o.e (o.e.symm ⟨_, hN⟩)) : Matrix (Fin n) (Fin n) X) * x.wX X w = P`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `show x.wiX X w * (x.wX X w * P * x.wiX X w) * x.wX X w = P`.

Simplify using `only [Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `hk : D.π (Sum.inl w) (o.e.symm ⟨_, hN⟩) = 0` using `(o.kerV w _).2 (fun i j hji => by rw [hconj]; exact hP0 i j (Or.inl hji))`. Establish `hg0 : g.f (o.e.symm ⟨_, hN⟩) = g.f m`. Apply `o''.e.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hg (o.e.symm ⟨_, hN⟩), LinearEquiv.apply_symm_apply]`. Use `show (x.wX X w * P * x.wiX X w).map v = _`. Rewrite using `[(map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w v P).2, hP]`. Simplify using `only [Matrix.mul_assoc, h2'', Matrix.mul_one]`.

Rewrite using `[← Matrix.mul_assoc, h2'', Matrix.one_mul]`. Establish `hdiff : g.f (m - o.e.symm ⟨_, hN⟩) = 0` using `by rw [map_sub, hg0, sub_self]`. Take `⟨m', hm'⟩` from `(ex _).1 hdiff`. Use `⟨D'.π _ m', (f.comm _ m').trans ?_⟩` and prove the remaining obligations. Rewrite using `[hm', map_sub, hk, sub_zero]`.

Establish `h1 : g.f m = 0` using `o''.kerU w (by rw [hq, map_zero])`. Take `⟨m', hm'⟩` from `(ex m).1 h1`. Conclude with `⟨D'.π _ m', (f.comm _ m').trans (congrArg _ hm')⟩`. Introduce and unpack `⟨q', rfl⟩`. Take `⟨m', rfl⟩` from `D'.surj w q'`.

Rewrite using `[f.comm, g.comm, (ex (f.f m')).2 ⟨m', rfl⟩, map_zero]`.
-/
theorem UpperTheory.V.Pa.B2.odSES :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X' : Type) [CommRing X'] [Algebra x.A X'] (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D' D D'' : Dat x.A (plOf G)) (o' : IsOd h x X' D') (o : IsOd h x X D) (o'' : IsOd h x X'' D'') (u : X' →ₗ[x.A] X) (v : X →ₗ[x.A] X'') (f : D'.Hom D) (g : D.Hom D''), Induced o' o u f → Induced o o'' v g → Function.Injective u → Function.Exact u v → Function.Surjective v → Dat.SES f g := by
  intro l _ L G G0 h n x X' _ _ X _ _ X'' _ _ D' D D'' o' o o'' u v f g hf hg hu hex hv
  have inj : Function.Injective f.f := by
    intro m1 m2 h12
    apply o'.e.injective
    apply Subtype.ext
    have e1 := hf m1
    rw [h12, hf m2] at e1
    ext i j
    exact hu (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X => M i j) e1.symm)
  have ex : Function.Exact f.f g.f := by
    intro m
    constructor
    · intro hgm
      have h0 : (↑(o.e m) : Matrix (Fin n) (Fin n) X).map v = 0 := by
        rw [← hg m, hgm]; simp
      obtain ⟨N', hN'0, hN'⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range u (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o.e m))
        (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o.e m).2 i j hij)
        (fun i j _ => (hex _).1 (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X'' => M i j) h0))
      refine ⟨o'.e.symm ⟨N', (mem_od_iff_entry_eq_zero_of_same_block _).2 hN'0⟩, ?_⟩
      apply o.e.injective
      apply Subtype.ext
      rw [hf, LinearEquiv.apply_symm_apply]
      exact hN'
    · rintro ⟨m', rfl⟩
      apply o''.e.injective
      apply Subtype.ext
      rw [hg, hf, map_zero]
      ext i j
      simpa using (hex _).2 ⟨_, rfl⟩
  have surj : Function.Surjective g.f := by
    intro m''
    obtain ⟨N, hN0, hN⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o''.e m''))
      (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e m'').2 i j hij) (fun i j _ => hv _)
    refine ⟨o.e.symm ⟨N, (mem_od_iff_entry_eq_zero_of_same_block _).2 hN0⟩, ?_⟩
    apply o''.e.injective
    apply Subtype.ext
    rw [hg, LinearEquiv.apply_symm_apply]
    exact hN
  refine ⟨inj, ex, surj, ?_, ?_⟩
  · intro w
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := D'.surj w q
    rw [f.comm] at hq
    rcases w with w | w
    · rw [o'.kerV]
      rw [o.kerV] at hq
      intro i j hji
      have e := hq i j hji
      rw [hf, ← (map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w u _).1, Matrix.map_apply] at e
      exact hu (by rw [map_zero]; exact e)
    · have h1 : f.f m = 0 := o.kerU w (by rw [hq, map_zero])
      rw [inj (h1.trans (map_zero f.f).symm), map_zero]
  · intro w q
    constructor
    · intro hq
      obtain ⟨m, rfl⟩ := D.surj w q
      rw [g.comm] at hq
      rcases w with w | w
      · have hlow := (o''.kerV w (g.f m)).1 hq
        obtain ⟨P, hP0, hP⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => j < i ∨ x.ty w i = x.ty w j)
          (x.wiX X'' w * (↑(o''.e (g.f m)) : Matrix (Fin n) (Fin n) X'') * x.wX X'' w)
          (fun i j hij => hij.elim (hlow i j) (wiX_mul_mul_wX_eq_zero_of_ty_eq x w _ ((mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e (g.f m)).2) i j))
          (fun i j _ => hv _)
        have hN : x.wX X w * P * x.wiX X w ∈ Od x.A X n x.a :=
          (mem_od_iff_entry_eq_zero_of_same_block _).2 (fun i j hij => wX_mul_mul_wiX_eq_zero_of_same_block x w P (fun k l hkl => hP0 k l (Or.inr hkl)) i j hij)
        obtain ⟨h1, h2⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X)
        obtain ⟨h1'', h2''⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X'')
        have hconj : x.wiX X w * (↑(o.e (o.e.symm ⟨_, hN⟩)) : Matrix (Fin n) (Fin n) X) * x.wX X w = P := by
          rw [LinearEquiv.apply_symm_apply]
          show x.wiX X w * (x.wX X w * P * x.wiX X w) * x.wX X w = P
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hk : D.π (Sum.inl w) (o.e.symm ⟨_, hN⟩) = 0 :=
          (o.kerV w _).2 (fun i j hji => by rw [hconj]; exact hP0 i j (Or.inl hji))
        have hg0 : g.f (o.e.symm ⟨_, hN⟩) = g.f m := by
          apply o''.e.injective
          apply Subtype.ext
          rw [hg (o.e.symm ⟨_, hN⟩), LinearEquiv.apply_symm_apply]
          show (x.wX X w * P * x.wiX X w).map v = _
          rw [(map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w v P).2, hP]
          simp only [Matrix.mul_assoc, h2'', Matrix.mul_one]
          rw [← Matrix.mul_assoc, h2'', Matrix.one_mul]
        have hdiff : g.f (m - o.e.symm ⟨_, hN⟩) = 0 := by rw [map_sub, hg0, sub_self]
        obtain ⟨m', hm'⟩ := (ex _).1 hdiff
        refine ⟨D'.π _ m', (f.comm _ m').trans ?_⟩
        rw [hm', map_sub, hk, sub_zero]
      · have h1 : g.f m = 0 := o''.kerU w (by rw [hq, map_zero])
        obtain ⟨m', hm'⟩ := (ex m).1 h1
        exact ⟨D'.π _ m', (f.comm _ m').trans (congrArg _ hm')⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨m', rfl⟩ := D'.surj w q'
      rw [f.comm, g.comm, (ex (f.f m')).2 ⟨m', rfl⟩, map_zero]
