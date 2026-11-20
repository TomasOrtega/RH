import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib]`. Use `W.sum_mem fun l _ => ?_` and prove the remaining obligations. Establish `h1 : ((a l - a' l : ℤ) : ZMod g) = 0` using `by push_cast; rw [h l, sub_self]`. Take `⟨t, ht⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1`. Rewrite using `[← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]`.

Conclude with `W.zsmul_mem (hu l) t`.
-/
theorem cong_zsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℤ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  rw [← Finset.sum_sub_distrib]
  refine W.sum_mem fun l _ => ?_
  have h1 : ((a l - a' l : ℤ) : ZMod g) = 0 := by push_cast; rw [h l, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]
  exact W.zsmul_mem (hu l) t

/- English proof (translation)
Use `cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)` as an intermediate fact. Simplify `this` using `only [natCast_zsmul]`.
-/
theorem cong_nsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℕ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  have := cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)
  simpa only [natCast_zsmul] using this

/- English proof (translation)
Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem sum_nsmul_sum {V : Type*} [AddCommGroup V] {r : ℕ} (u : Fin r → V) (a : Fin r → ℕ)
    (b : Fin r → Fin r → ℕ) :
    ∑ j, a j • ∑ l, b l j • u l = ∑ l, (∑ j, a j * b l j) • u l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `only [map_nsmul]`. Establish `e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) + ∑ j, (c j i).val • ∑ l, (M l j).val • u l`. Rewrite using `[← Finset.sum_add_distrib]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[← smul_add, sub_add_cancel]`. Rewrite using `[e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]`. Use `W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)` and prove the remaining obligations. Establish `e2 : c * (d * M * c) = M * c` using `by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]`.

Establish `e3` using `congrFun (congrFun e2 l) i`. Rewrite `e3` using `[Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]`. Rewrite using `[show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
theorem rebase_rel {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (F : V →+ V) (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (M c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1)
    (h : ∀ i, F (u i) - ∑ j, (M j i).val • u j ∈ W) (i : Fin r) :
    F (∑ j, (c j i).val • u j) - ∑ m, ((d * M * c) m i).val • ∑ l, (c l m).val • u l ∈ W := by
  rw [map_sum]
  simp only [map_nsmul]
  have e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) +
      ∑ j, (c j i).val • ∑ l, (M l j).val • u l := by
    rw [← Finset.sum_add_distrib]; congr 1; funext j; rw [← smul_add, sub_add_cancel]
  rw [e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]
  refine W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)
  have e2 : c * (d * M * c) = M * c := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]
  have e3 := congrFun (congrFun e2 l) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at e3
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/- English proof (translation)
Use `⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩` and prove the remaining obligations. Establish `e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j = ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j`. Simplify using `only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Rewrite using `[e1]`.

Use `cong_zsmul W u hu _ _ fun j => ?_` and prove the remaining obligations. Establish `e2` using `congrFun (congrFun hcd j) j`. Use `push_cast`. Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id]`. Establish `e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g)`.

Simplify using `only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e3, hcd]`. Simplify using `[Matrix.one_apply]`.
-/
theorem rebase_span {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1) (a : Fin r → ℤ) :
    ∃ e : Fin r → ℤ, ∑ j, a j • u j - ∑ m, e m • ∑ j, (c j m).val • u j ∈ W := by
  refine ⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩
  have e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j =
      ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j := by
    simp only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  refine cong_zsmul W u hu _ _ fun j => ?_
  have e2 := congrFun (congrFun hcd j) j
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hcd]
  simp [Matrix.one_apply]

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[incl, map_sum, map_nsmul, Finset.sum_apply]`.
-/
theorem incl_sum_nsmul (X : HidaSetting D) {r : ℕ} (a : Fin r → ℕ) (x : Fin r → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j, a j • x j) = ∑ j, a j • incl X.B.I (x j) := by
  funext t
  simp [incl, map_sum, map_nsmul, Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[incl, map_nsmul]`.
-/
theorem incl_nsmul (X : HidaSetting D) (a : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (a • x) = a • incl X.B.I x := by
  funext t
  simp [incl, map_nsmul]

/- English proof (translation)
Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩` and prove the remaining obligations.
-/
theorem nsmul_mem_wLat (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    g • y ∈ wLat X w := by
  apply Submodule.subset_span
  refine ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩`.
-/
theorem incl_mem_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {y : Fin X.B.I.n → X.B.I.E}
    (hy : y ∈ wLat X w) : incl X.B.I y ∈ wLf X w :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

/- English proof (translation)
Introduce `D X red b c hg hf`. Use `⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩` and prove the remaining obligations. Use `haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩`. Take `⟨⟨hbL, hbspan⟩, hrel⟩` from `hf kv`. Establish `hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) * (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1` using `Units.mul_inv (c kv)`.

Establish `hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup` using `fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)`. Use `⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _`. Take `⟨a, ha⟩` from `hbspan y hy`. Take `⟨e, he⟩` from `rebase_span _ (b kv) hgL _ _ hcd a`.

Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `h2` using `Submodule.add_mem _ ha he`. Simplify using `only [Int.cast_smul_eq_zsmul] at h2 ⊢`. Rewrite `h2` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup` using `fun j => by`.

Rewrite using `[← incl_nsmul]`. Conclude with `incl_mem_wLf X _ (hgL j)`. Establish `hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) - ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup` using `fun i => by`. Use `hrel k hk i` as an intermediate fact. Simplify using `only [Nat.cast_smul_eq_nsmul] at this`.

Conclude with `this`. Establish `key` using `rebase_rel _ _ _ hu _ _ _ hcd hM i`. Simplify using `only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key`. Simplify using `only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]`. Conclude with `key`.
-/
theorem fixRed_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  intro D X red b c hg hf
  classical
  refine ⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨⟨hbL, hbspan⟩, hrel⟩ := hf kv
  have hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.mul_inv (c kv)
  have hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup :=
    fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)
  refine ⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _
  · obtain ⟨a, ha⟩ := hbspan y hy
    obtain ⟨e, he⟩ := rebase_span _ (b kv) hgL _ _ hcd a
    refine ⟨e, ?_⟩
    have h2 := Submodule.add_mem _ ha he
    simp only [Int.cast_smul_eq_zsmul] at h2 ⊢
    rwa [sub_add_sub_cancel] at h2
  · have hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun j => by
      rw [← incl_nsmul]; exact incl_mem_wLf X _ (hgL j)
    have hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) -
        ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈
        (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun i => by
      have := hrel k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this
    have key := rebase_rel _ _ _ hu _ _ _ hcd hM i
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key
    simp only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
    exact key

end GlobalTheory.Mem.SRe

end
