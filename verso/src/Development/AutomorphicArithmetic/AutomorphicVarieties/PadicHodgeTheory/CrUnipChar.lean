import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.CrUnipChar

variable {Q A B : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup B] [Module Q B]

private def ctr (lam : A →ₗ[Q] Q) : A ⊗[Q] B →ₗ[Q] B :=
  (TensorProduct.lid Q B).toLinearMap ∘ₗ lam.rTensor B

/- English proof (translation)
Simplify using `[ctr]`.
-/
private theorem ctr_tmul (lam : A →ₗ[Q] Q) (a : A) (b : B) : ctr lam (a ⊗ₜ[Q] b) = lam a • b := by
  simp [ctr]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [ctr_tmul, ← smul_tmul, ← sum_tmul, Basis.coord_apply, Basis.sum_repr]`. Consider the case `add y z hy hz`.

Simplify using `only [map_add, tmul_add, Finset.sum_add_distrib]`. Rewrite using `[← hy, ← hz]`.
-/
private theorem eq_sum [Module.Finite Q A] (x : A ⊗[Q] B) :
    x = ∑ i, Module.finBasis Q A i ⊗ₜ[Q] ctr ((Module.finBasis Q A).coord i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [ctr_tmul, ← smul_tmul, ← sum_tmul, Basis.coord_apply, Basis.sum_repr]
  | add y z hy hz =>
    simp only [map_add, tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ lam`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simpa [ctr_tmul] using F.smul_mem _ b.2`.

Consider the case `add y z hy hz => simpa only [map_add] using F.add_mem hy hz`. Introduce `h`. Rewrite using `[eq_sum x]`. Conclude with `Submodule.sum_mem _ fun i _ => ⟨Module.finBasis Q A i ⊗ₜ ⟨_, h ((Module.finBasis Q A).coord i)⟩, by simp⟩`.
-/
private theorem mem_iff [Module.Finite Q A] (F : Submodule Q B) (x : A ⊗[Q] B) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) F.subtype) ↔
      ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F := by
  constructor
  · rintro ⟨y, rfl⟩ lam
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simpa [ctr_tmul] using F.smul_mem _ b.2
    | add y z hy hz => simpa only [map_add] using F.add_mem hy hz
  · intro h
    rw [eq_sum x]
    exact Submodule.sum_mem _ fun i _ => ⟨Module.finBasis Q A i ⊗ₜ ⟨_, h ((Module.finBasis Q A).coord i)⟩, by simp⟩

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [ctr_tmul, sub_mul, sub_smul]`. Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Normalize the expressions using the abelian group laws.
-/
private theorem ctr_map (lam : A →ₗ[Q] Q) (u : A) (s : B →ₗ[Q] B) (x : A ⊗[Q] B) :
    ctr lam (AlgebraTensorModule.map (u • (LinearMap.id : A →ₗ[A] A)) s x) =
      s (ctr lam x) + s (ctr (lam ∘ₗ LinearMap.mulLeft Q (u - 1)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ctr_tmul, sub_mul, sub_smul]
  | add y z hy hz => simp only [map_add, hy, hz]; abel

/- English proof (translation)
Use `haveI : IsNoetherianRing A := isNoetherian_of_tower Q inferInstance`. Take `⟨k, hk⟩` from `IsNoetherianRing.isNilpotent_nilradical A`. Establish `key : ∀ (j : ℕ) (lam : A →ₗ[Q] Q), (∀ a ∈ nilradical A ^ j, lam a = 0) → ctr lam x ∈ F'`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `lam h`. Establish `: lam = 0` using `LinearMap.ext fun a => h a (by simp)`. Simplify using `[this, ctr]`. Consider the case `succ j ih`.

Introduce `lam h`. Use `hT _ (hF lam) fun g => ?_` and prove the remaining obligations. Establish `e` using `ctr_map lam (u g) (s g) x`. Rewrite `e` using `[hx g]`. Establish `h2` using `hs g _ (ih (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) fun a ha => h _ (by`.

Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (mem_nilradical.2 (hu g)) ha))`. Establish `e2 : s g (ctr lam x) - ctr lam x = -s g (ctr (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) x)`. Rewrite using `[eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← e, sub_self]`. Rewrite using `[e2]`.

Conclude with `F'.neg_mem h2`. Use `key k lam fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[hk]`. Rewrite using `[(Submodule.mem_bot _).1 ha, map_zero]`.
-/
private theorem step [Module.Finite Q A] {G : Type} (u : G → A) (hu : ∀ g, IsNilpotent (u g - 1))
    (s : G → B →ₗ[Q] B) (F F' : Submodule Q B) (hs : ∀ g, ∀ b ∈ F', s g b ∈ F')
    (hT : ∀ b ∈ F, (∀ g, s g b - b ∈ F') → b ∈ F') (x : A ⊗[Q] B)
    (hx : ∀ g, AlgebraTensorModule.map (u g • (LinearMap.id : A →ₗ[A] A)) (s g) x = x)
    (hF : ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F) (lam : A →ₗ[Q] Q) : ctr lam x ∈ F' := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower Q inferInstance
  obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical A
  have key : ∀ (j : ℕ) (lam : A →ₗ[Q] Q), (∀ a ∈ nilradical A ^ j, lam a = 0) → ctr lam x ∈ F' := by
    intro j
    induction j with
    | zero =>
      intro lam h
      have : lam = 0 := LinearMap.ext fun a => h a (by simp)
      simp [this, ctr]
    | succ j ih =>
      intro lam h
      refine hT _ (hF lam) fun g => ?_
      have e := ctr_map lam (u g) (s g) x
      rw [hx g] at e
      have h2 := hs g _ (ih (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) fun a ha => h _ (by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (mem_nilradical.2 (hu g)) ha))
      have e2 : s g (ctr lam x) - ctr lam x = -s g (ctr (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) x) := by
        rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← e, sub_self]
      rw [e2]
      exact F'.neg_mem h2
  refine key k lam fun a ha => ?_
  rw [hk] at ha
  rw [(Submodule.mem_bot _).1 ha, map_zero]

/- English proof (translation)
Establish `h1 : IsNilpotent (∑ i ∈ Finset.range n, (u ^ i - 1))`. Use `isNilpotent_sum fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_one_dvd_pow_sub_one u i`. Rewrite using `[hc]`. Conclude with `(Commute.all _ _).isNilpotent_mul_right hu`.

Establish `h2 : IsUnit ((n : ℕ) : A)`. Rewrite using `[← map_natCast (algebraMap Q A)]`. Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _`. Establish `h3 : IsUnit (∑ i ∈ Finset.range n, u ^ i)`. Use `h1.isUnit_add_left_of_commute h2 (Commute.all _ _)` as an intermediate fact.

Simplify `this` using `[Finset.sum_sub_distrib]`. Establish `h4` using `geom_sum_mul u n`. Rewrite `h4` using `[h, sub_self]`. Conclude with `sub_eq_zero.1 (h3.mul_right_eq_zero.1 h4)`.
-/
private theorem eq_one_of_pow [CharZero Q] {u : A} (hu : IsNilpotent (u - 1)) {n : ℕ} (hn : n ≠ 0)
    (h : u ^ n = 1) : u = 1 := by
  have h1 : IsNilpotent (∑ i ∈ Finset.range n, (u ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one u i
    rw [hc]
    exact (Commute.all _ _).isNilpotent_mul_right hu
  have h2 : IsUnit ((n : ℕ) : A) := by
    rw [← map_natCast (algebraMap Q A)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  have h3 : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa [Finset.sum_sub_distrib] using this
  have h4 := geom_sum_mul u n
  rw [h, sub_self] at h4
  exact sub_eq_zero.1 (h3.mul_right_eq_zero.1 h4)

/- English proof (translation)
Take `⟨T⟩` from `tiedP l`. Set `F : ℤ → Submodule ℚ_[l] (Bdr l)` to `fun a => (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]`. Establish `hF : ∀ a b, b ∈ F a ↔ b ∈ ((PP l).PD K).Fil a` using `fun a b => by`. Use `(PP l).PD_Fil (botExt l) K a` as an intermediate fact. Conclude with `Set.ext_iff.1 this b`.

Establish `hanti : Antitone F` using `antitone_int_of_succ_le fun a b hb => (hF _ _).2 (((PP l).PD K).Fil_anti a ((hF _ _).1 hb))`. Establish `up : ∀ x ∈ Ddr φ (chRep κ), ∀ n : ℤ, n ≠ 0 → (∀ lam, ctr lam x ∈ F n) → ∀ lam, ctr lam x ∈ F (n + 1)`. Introduce `x hx n hn h`. Use `step (fun g => (κ g : A)) hκ (fun g => ((PP l).actQdR (φ g)).toLinearMap) (F n) (F (n + 1)) (fun g b hb => ?_) (fun b hb hg => ?_) x (fun g => ?_) h` and prove the remaining obligations. Use `((PP l).PD K).Fil_G ⟨φ g, by rw [← hK]; exact ⟨g, rfl⟩⟩ _ _ ((hF _ _).1 hb)` as an intermediate fact.

Rewrite `this` using `[(PP l).PD_actdR]`. Conclude with `(hF _ _).2 this`. Take `⟨Θ⟩` from `GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T`. Take `⟨c, -, -, h0, h1⟩` from `GlobalTheory.DRFil.graded_invariants T Θ K n b ((hF _ _).1 hb) fun g => by`. Take `⟨g', hg'⟩ : (g : GQ l) ∈ φ.range` from `by rw [hK]; exact g.2`.

Rewrite using `[(PP l).PD_actdR, ← hg']`. Conclude with `(hF _ _).1 (hg g')`. Rewrite `h1` using `[h0 hn, sub_zero]`. Conclude with `(hF _ _).2 h1`. Use `(Submodule.mem_iInf _).1 hx g` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `this`. Prove the components needed by the constructor for the conclusion. Use `inf_eq_left.2 fun x hx => (mem_iff (F 0) x).2 ?_` and prove the remaining obligations. Establish `ex : ∃ a : ℤ, ∀ lam, ctr lam x ∈ F a` using `by clear hx`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, fun lam => by simp⟩`. Consider the case `tmul a b`. Take `⟨n, hn⟩` from `((PP l).PD K).Fil_exh b`. Conclude with `⟨n, fun lam => by rw [ctr_tmul]; exact (F n).smul_mem _ ((hF _ _).2 hn)⟩`.

Consider the case `add y z hy hz`. Take `⟨a, ha⟩` from `hy`. Take `⟨b, hb⟩` from `hz`. Conclude with `⟨min a b, fun lam => by`. Rewrite using `[map_add]`.

Conclude with `(F _).add_mem (hanti (min_le_left _ _) (ha lam)) (hanti (min_le_right _ _) (hb lam))⟩`. Take `⟨a, ha⟩` from `ex`. Break down `le_total 0 a with h | h` into its components or cases. Conclude with `fun lam => hanti h (ha lam)`. Establish `key : ∀ m, a ≤ m → m ≤ 0 → ∀ lam, ctr lam x ∈ F m`.

Introduce `m hm`. Proceed by induction on `m, hm using Int.le_induction with`. Consider the case `base => exact fun _ => ha`. Consider the case `succ m hm ih => exact fun h => up x hx m (by omega) (ih (by omega))`. Conclude with `key 0 h le_rfl`.

Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `(mem_iff (F 1) x).1 hx.2`. Establish `key : ∀ m : ℤ, 1 ≤ m → ∀ lam, ctr lam x ∈ F m`. Introduce `m hm`. Proceed by induction on `m, hm using Int.le_induction with`.

Consider the case `base => exact h1`. Consider the case `succ m hm ih => exact up x hx.1 m (by omega) ih`. Establish `h0 : ∀ lam, ctr lam x = 0` using `fun lam => ((PP l).PD K).Fil_sep _ fun a => (hF _ _).1 (hanti (le_max_left a 1) (key _ (le_max_right _ _) lam))`. Rewrite using `[Submodule.mem_bot, eq_sum x]`. Simplify using `[h0]`.
-/
private theorem fil {l : ℕ} [Fact l.Prime] {G : Type} [Group G] (φ : G →* GQ l) (K : FinExt l)
    (hK : φ.range = GK K) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] (κ : G →* Aˣ)
    (hκ : ∀ g, IsNilpotent ((κ g : A) - 1)) :
    FilD φ (chRep κ) 0 = Ddr φ (chRep κ) ∧ FilD φ (chRep κ) 1 = ⊥ := by
  obtain ⟨T⟩ := tiedP l
  let F : ℤ → Submodule ℚ_[l] (Bdr l) := fun a => (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]
  have hF : ∀ a b, b ∈ F a ↔ b ∈ ((PP l).PD K).Fil a := fun a b => by
    have := (PP l).PD_Fil (botExt l) K a
    exact Set.ext_iff.1 this b
  have hanti : Antitone F := antitone_int_of_succ_le fun a b hb =>
    (hF _ _).2 (((PP l).PD K).Fil_anti a ((hF _ _).1 hb))
  have up : ∀ x ∈ Ddr φ (chRep κ), ∀ n : ℤ, n ≠ 0 → (∀ lam, ctr lam x ∈ F n) →
      ∀ lam, ctr lam x ∈ F (n + 1) := by
    intro x hx n hn h
    refine step (fun g => (κ g : A)) hκ (fun g => ((PP l).actQdR (φ g)).toLinearMap) (F n) (F (n + 1))
      (fun g b hb => ?_) (fun b hb hg => ?_) x (fun g => ?_) h
    · have := ((PP l).PD K).Fil_G ⟨φ g, by rw [← hK]; exact ⟨g, rfl⟩⟩ _ _ ((hF _ _).1 hb)
      rw [(PP l).PD_actdR] at this
      exact (hF _ _).2 this
    · obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
      obtain ⟨c, -, -, h0, h1⟩ := GlobalTheory.DRFil.graded_invariants T Θ K n b ((hF _ _).1 hb) fun g => by
        obtain ⟨g', hg'⟩ : (g : GQ l) ∈ φ.range := by rw [hK]; exact g.2
        rw [(PP l).PD_actdR, ← hg']
        exact (hF _ _).1 (hg g')
      rw [h0 hn, sub_zero] at h1
      exact (hF _ _).2 h1
    · have := (Submodule.mem_iInf _).1 hx g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      exact this
  constructor
  · refine inf_eq_left.2 fun x hx => (mem_iff (F 0) x).2 ?_
    have ex : ∃ a : ℤ, ∀ lam, ctr lam x ∈ F a := by
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, fun lam => by simp⟩
      | tmul a b =>
        obtain ⟨n, hn⟩ := ((PP l).PD K).Fil_exh b
        exact ⟨n, fun lam => by rw [ctr_tmul]; exact (F n).smul_mem _ ((hF _ _).2 hn)⟩
      | add y z hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨min a b, fun lam => by
          rw [map_add]
          exact (F _).add_mem (hanti (min_le_left _ _) (ha lam)) (hanti (min_le_right _ _) (hb lam))⟩
    obtain ⟨a, ha⟩ := ex
    rcases le_total 0 a with h | h
    · exact fun lam => hanti h (ha lam)
    have key : ∀ m, a ≤ m → m ≤ 0 → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.le_induction with
      | base => exact fun _ => ha
      | succ m hm ih => exact fun h => up x hx m (by omega) (ih (by omega))
    exact key 0 h le_rfl
  · refine eq_bot_iff.2 fun x hx => ?_
    have h1 := (mem_iff (F 1) x).1 hx.2
    have key : ∀ m : ℤ, 1 ≤ m → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.le_induction with
      | base => exact h1
      | succ m hm ih => exact up x hx.1 m (by omega) ih
    have h0 : ∀ lam, ctr lam x = 0 := fun lam => ((PP l).PD K).Fil_sep _ fun a =>
      (hF _ _).1 (hanti (le_max_left a 1) (key _ (le_max_right _ _) lam))
    rw [Submodule.mem_bot, eq_sum x]
    simp [h0]

end UpperTheory.V.Loc.CrUnipChar

open UpperTheory.V.Loc.CrUnipChar in
/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ A _ _ _ _ _ _ κ hc hκ H hH hcr g hg`. Establish `hφ' : IsOpenEmbedding (φ.comp H.subtype)` using `hφ.comp hH.isOpenEmbedding_subtypeVal`. Take `⟨K, -, -, -, -, hK, hi, -⟩` from `openField (φ.comp H.subtype) hφ'`. Use `haveI := K.2`. Take `⟨f0, f1⟩` from `fil (φ.comp H.subtype) K hK (κ.comp H.subtype) fun h => hκ h`.

Establish `hca : ReciprocityTheory.Gal.ContAction (chRep (κ.comp H.subtype))`. Unfold `ReciprocityTheory.Gal.ContAction`. Conclude with `((hc.comp continuous_subtype_val).comp continuous_fst).mul continuous_snd`. Establish `hw` using `crWt0 (φ.comp H.subtype) hφ' (chRep (κ.comp H.subtype)) hca hcr f0 f1`. Take `⟨n, hn, -, h, hh⟩` from `(φ.comp H.subtype).range.exists_pow_mem_of_index_ne_zero (by rw [hi]; exact finrank_pos.ne') (φ g)`.

Establish `e : (h : G) = g ^ n` using `hφ.injective (by rw [map_pow]; exact hh)`. Establish `h1` using `LinearMap.congr_fun (hw h (by rw [hh]; exact (Iq l).pow_mem hg n)) 1`. Establish `h2 : (κ g : A) ^ n = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, ← e]`. Simplify `h1` using `[chRep]`.

Conclude with `Units.ext (eq_one_of_pow (Q := ℚ_[l]) (hκ g) hn.ne' h2)`.
-/
theorem UpperTheory.V.Loc.crUnipChar :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A] (κ : G →* Aˣ), Continuous (fun g => (κ g : A)) → (∀ g, IsNilpotent ((κ g : A) - 1)) → ∀ H : Subgroup G, IsOpen (H : Set G) → CrOn φ (chRep κ) H → ∀ g, φ g ∈ Iq l → κ g = 1 := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ _ _ κ hc hκ H hH hcr g hg
  have hφ' : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K, -, -, -, -, hK, hi, -⟩ := openField (φ.comp H.subtype) hφ'
  haveI := K.2
  obtain ⟨f0, f1⟩ := fil (φ.comp H.subtype) K hK (κ.comp H.subtype) fun h => hκ h
  have hca : ReciprocityTheory.Gal.ContAction (chRep (κ.comp H.subtype)) := by
    unfold ReciprocityTheory.Gal.ContAction
    exact ((hc.comp continuous_subtype_val).comp continuous_fst).mul continuous_snd
  have hw := crWt0 (φ.comp H.subtype) hφ' (chRep (κ.comp H.subtype)) hca hcr f0 f1
  obtain ⟨n, hn, -, h, hh⟩ := (φ.comp H.subtype).range.exists_pow_mem_of_index_ne_zero
    (by rw [hi]; exact finrank_pos.ne') (φ g)
  have e : (h : G) = g ^ n := hφ.injective (by rw [map_pow]; exact hh)
  have h1 := LinearMap.congr_fun (hw h (by rw [hh]; exact (Iq l).pow_mem hg n)) 1
  have h2 : (κ g : A) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e]
    simpa [chRep] using h1
  exact Units.ext (eq_one_of_pow (Q := ℚ_[l]) (hκ g) hn.ne' h2)
