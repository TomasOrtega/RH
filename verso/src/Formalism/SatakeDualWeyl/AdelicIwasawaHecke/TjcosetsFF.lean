import Formalism.SatakeDualWeyl.StatementE

noncomputable section

open Matrix

namespace Formalism.UG.P

section FF

variable {𝔽 : Type} [Field 𝔽]

def TjcosetsFr (m n : ℕ) (𝔽 : Type) : Type := Fin m → Fin n → 𝔽

instance tjcosets_act (m n : ℕ) : MulAction (GL (Fin n) 𝔽) (TjcosetsFr m n 𝔽) where
  smul g w := fun i => (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i
  one_smul w := by
    show (fun i => ((1 : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i) = w
    funext i
    simp
  mul_smul g h w := by
    show (fun i => ((g * h : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i) =
      (fun i => (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ ((h : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i))
    funext i
    simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tjcosets_smul_apply {m n : ℕ} (g : GL (Fin n) 𝔽) (w : TjcosetsFr m n 𝔽) (i : Fin m) :
    (g • w) i = (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i := rfl

def tjcosets_idx (n j : ℕ) (i : Fin (n - j)) : Fin n := ⟨j + i, by omega⟩

/- English proof (translation)
Introduce `a b h`. Establish `h1` using `congrArg Fin.val h`. Simplify using `only [tjcosets_idx] at h1`. Conclude with `Fin.ext (by omega)`.
-/
theorem tjcosets_idx_injective (n j : ℕ) : Function.Injective (tjcosets_idx n j) := by
  intro a b h
  have h1 := congrArg Fin.val h
  simp only [tjcosets_idx] at h1
  exact Fin.ext (by omega)

def standardBasisTuple (n j : ℕ) : TjcosetsFr (n - j) n 𝔽 := fun i => Pi.single (tjcosets_idx n j i) 1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[tjcosets_smul_apply, standardBasisTuple, Matrix.mulVec_single_one]`.
-/
theorem GL_smul_standard_tuple (n j : ℕ) (g : GL (Fin n) 𝔽) :
    (g • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)) =
      fun i => (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j i) := by
  funext i
  rw [tjcosets_smul_apply, standardBasisTuple, Matrix.mulVec_single_one]

def tjcosets_parMon (n j : ℕ) : Submonoid (GL (Fin n) 𝔽) where
  carrier := {g | ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) 𝔽) a b = 0}
  one_mem' := by
    intro a b ha hb
    have : a ≠ b := by intro h; subst h; omega
    simp [this]
  mul_mem' := by
    intro g h hg hh a b ha hb
    simp only [Units.val_mul, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : (c : ℕ) < j
    · rw [hh c b hc hb, mul_zero]
    · rw [hg a c ha (by omega), zero_mul]

/- English proof (translation)
Establish `hpos` using `(isOfFinOrder_of_finite x).orderOf_pos`. Establish `e : x ^ (orderOf x - 1) = x⁻¹` using `eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])`. Rewrite using `[← e]`. Conclude with `S.pow_mem hx _`.
-/
theorem tjcosets_inv_mem_of_finite {G : Type} [Group G] [Finite G] (S : Submonoid G) {x : G}
    (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpos := (isOfFinOrder_of_finite x).orderOf_pos
  have e : x ^ (orderOf x - 1) = x⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
  rw [← e]
  exact S.pow_mem hx _

def tjcosets_par [Finite 𝔽] (n j : ℕ) : Subgroup (GL (Fin n) 𝔽) :=
  { tjcosets_parMon n j with
    inv_mem' := fun hx => tjcosets_inv_mem_of_finite _ hx }

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem tjcosets_mem_par [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    g ∈ tjcosets_par n j ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) 𝔽) a b = 0 := Iff.rfl

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Use `⟨fun i => v (Fin.cast (Nat.zero_add k) i), hv.comp _ (Fin.cast_injective _), fun i => ?_⟩` and prove the remaining obligations. Use `congr 1`. Use `ext`.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Take `⟨s, hs, hsv⟩` from `ih (by omega)`. Take `⟨x, hx⟩` from `exists_linearIndependent_cons_of_lt_finrank hs (by rw [Module.finrank_fin_fun]; omega)`. Establish `hc : d + 1 + k = d + k + 1` using `by omega`.

Use `⟨fun i => (Fin.cons x s : Fin (d + k + 1) → Fin N → 𝔽) (Fin.cast hc i), hx.comp _ (Fin.cast_injective _), fun i => ?_⟩` and prove the remaining obligations. Establish `e : Fin.cast hc (Fin.natAdd (d + 1) i) = Fin.succ (Fin.natAdd d i)`. Use `ext`. Simplify using `only [Fin.coe_cast, Fin.coe_natAdd, Fin.val_succ]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [e, Fin.cons_succ]`. Conclude with `hsv i`.
-/
private theorem exists_linearIndependent_extension_fin (N : ℕ) (d k : ℕ) (hdk : d + k ≤ N) (v : Fin k → Fin N → 𝔽)
    (hv : LinearIndependent 𝔽 v) :
    ∃ s : Fin (d + k) → Fin N → 𝔽, LinearIndependent 𝔽 s ∧ ∀ i, s (Fin.natAdd d i) = v i := by
  induction d with
  | zero =>
    refine ⟨fun i => v (Fin.cast (Nat.zero_add k) i), hv.comp _ (Fin.cast_injective _), fun i => ?_⟩
    congr 1
    ext
    simp
  | succ d ih =>
    obtain ⟨s, hs, hsv⟩ := ih (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hs
      (by rw [Module.finrank_fin_fun]; omega)
    have hc : d + 1 + k = d + k + 1 := by omega
    refine ⟨fun i => (Fin.cons x s : Fin (d + k + 1) → Fin N → 𝔽) (Fin.cast hc i),
      hx.comp _ (Fin.cast_injective _), fun i => ?_⟩
    have e : Fin.cast hc (Fin.natAdd (d + 1) i) = Fin.succ (Fin.natAdd d i) := by
      ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.val_succ]
      omega
    simp only [e, Fin.cons_succ]
    exact hsv i

/- English proof (translation)
Take `⟨s, hs, hsw⟩` from `exists_linearIndependent_extension_fin n (n - (n - j)) (n - j) (by omega) w hw`. Establish `hc : n - (n - j) + (n - j) = n` using `by omega`. Use `⟨fun a => s (Fin.cast hc.symm a), hs.comp _ (Fin.cast_injective _), fun i => ?_⟩` and prove the remaining obligations. Establish `e : Fin.cast hc.symm (tjcosets_idx n j i) = Fin.natAdd (n - (n - j)) i`. Apply `Fin.ext` to reduce the goal to its premises.

Use `show j + (i : ℕ) = n - (n - j) + i`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show s (Fin.cast hc.symm (tjcosets_idx n j i)) = w i`. Rewrite using `[e, hsw]`.
-/
theorem tjcosets_extend [Finite 𝔽] (n j : ℕ) (w : Fin (n - j) → Fin n → 𝔽)
    (hw : LinearIndependent 𝔽 w) :
    ∃ s : Fin n → Fin n → 𝔽, LinearIndependent 𝔽 s ∧ ∀ i, s (tjcosets_idx n j i) = w i := by
  obtain ⟨s, hs, hsw⟩ := exists_linearIndependent_extension_fin n (n - (n - j)) (n - j) (by omega) w hw
  have hc : n - (n - j) + (n - j) = n := by omega
  refine ⟨fun a => s (Fin.cast hc.symm a), hs.comp _ (Fin.cast_injective _), fun i => ?_⟩
  have e : Fin.cast hc.symm (tjcosets_idx n j i) = Fin.natAdd (n - (n - j)) i := by
    apply Fin.ext
    show j + (i : ℕ) = n - (n - j) + i
    have := i.isLt
    omega
  show s (Fin.cast hc.symm (tjcosets_idx n j i)) = w i
  rw [e, hsw]

/- English proof (translation)
Conclude with `(Matrix.linearIndependent_cols_of_isUnit (Units.isUnit g)).comp _ (tjcosets_idx_injective n j)`.
-/
theorem GL_columns_linearIndependent [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    LinearIndependent 𝔽 (fun i => (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j i)) := by
  exact (Matrix.linearIndependent_cols_of_isUnit (Units.isUnit g)).comp _ (tjcosets_idx_injective n j)

/- English proof (translation)
Take `⟨s, hs, hsw⟩` from `tjcosets_extend n j w hw`. Set `A : Matrix (Fin n) (Fin n) 𝔽` to `Matrix.of fun a b => s b a`. Establish `hAc : A.col = s` using `by funext b a; rfl`. Establish `hA : IsUnit A` using `Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hAc]; exact hs)`. Use `⟨hA.unit, ?_⟩` and prove the remaining obligations.

Rewrite using `[GL_smul_standard_tuple]`. Use function extensionality and compare the values at `i`. Rewrite using `[IsUnit.unit_spec, hAc, hsw]`.
-/
theorem tjcosets_exists_smul [Finite 𝔽] (n j : ℕ) (w : TjcosetsFr (n - j) n 𝔽)
    (hw : LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)) :
    ∃ g : GL (Fin n) 𝔽, g • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w := by
  obtain ⟨s, hs, hsw⟩ := tjcosets_extend n j w hw
  let A : Matrix (Fin n) (Fin n) 𝔽 := Matrix.of fun a b => s b a
  have hAc : A.col = s := by funext b a; rfl
  have hA : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hAc]; exact hs)
  refine ⟨hA.unit, ?_⟩
  rw [GL_smul_standard_tuple]
  funext i
  rw [IsUnit.unit_spec, hAc, hsw]

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Rewrite using `[GL_smul_standard_tuple]`.

Conclude with `GL_columns_linearIndependent n j g`. Introduce `hw`. Conclude with `tjcosets_exists_smul n j w hw`.
-/
theorem tjcosets_orbit_gl [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽)} := by
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, rfl⟩
    rw [GL_smul_standard_tuple]
    exact GL_columns_linearIndependent n j g
  · intro hw
    exact tjcosets_exists_smul n j w hw

/- English proof (translation)
Use `ext`. Simplify using `only [tjcosets_idx]`. Use linear arithmetic over natural numbers and integers.
-/
theorem tjcosets_idx_sub (n j : ℕ) (b : Fin n) (hb : j ≤ (b : ℕ)) :
    tjcosets_idx n j ⟨b - j, by omega⟩ = b := by
  ext
  simp only [tjcosets_idx]
  omega

/- English proof (translation)
Introduce `g hg`. Rewrite `hg` using `[MulAction.mem_stabilizer_iff, GL_smul_standard_tuple]`. Rewrite using `[tjcosets_mem_par]`. Introduce `a b ha hb`. Establish `h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a = standardBasisTuple n j ⟨b - j, by omega⟩ a` using `congrFun (congrFun hg _) a`.

Simplify using `only [standardBasisTuple] at h1`. Rewrite `h1` using `[tjcosets_idx_sub n j b hb]`. Establish `hab : a ≠ b` using `by intro h; subst h; omega`. Rewrite `h1` using `[Pi.single_eq_of_ne hab]`. Simplify `h1` using `[Matrix.col]`.
-/
theorem tjcosets_stab_le_par [Finite 𝔽] (n j : ℕ) :
    MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) ≤
      tjcosets_par n j := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, GL_smul_standard_tuple] at hg
  rw [tjcosets_mem_par]
  intro a b ha hb
  have h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a
      = standardBasisTuple n j ⟨b - j, by omega⟩ a := congrFun (congrFun hg _) a
  simp only [standardBasisTuple] at h1
  rw [tjcosets_idx_sub n j b hb] at h1
  have hab : a ≠ b := by intro h; subst h; omega
  rw [Pi.single_eq_of_ne hab] at h1
  simpa [Matrix.col] using h1

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp⟩`. Establish `hp' : (p : GL (Fin n) 𝔽) • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w` using `hp`.

Rewrite `hp'` using `[GL_smul_standard_tuple]`. Substitute `hp'` using the available equality. Use `⟨GL_columns_linearIndependent n j (p : GL (Fin n) 𝔽), fun i a ha => ?_⟩` and prove the remaining obligations. Establish `h0` using `(tjcosets_mem_par n j (p : GL (Fin n) 𝔽)).1 p.2 a (tjcosets_idx n j i) ha (by simp [tjcosets_idx])`. Simplify `h0` using `[Matrix.col]`.

Introduce and unpack `⟨hw, hz⟩`. Take `⟨g, hg⟩` from `tjcosets_exists_smul n j w hw`. Establish `hg'` using `hg`. Rewrite `hg'` using `[GL_smul_standard_tuple]`. Establish `hgP : g ∈ tjcosets_par n j`.

Rewrite using `[tjcosets_mem_par]`. Introduce `a b ha hb`. Establish `h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a = w ⟨b - j, by omega⟩ a` using `congrFun (congrFun hg' _) a`. Rewrite `h1` using `[tjcosets_idx_sub n j b hb]`. Establish `h2` using `h1.trans (hz _ a ha)`.

Simplify `h2` using `[Matrix.col]`. Use `⟨⟨g, hgP⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def]`. Conclude with `hg`.
-/
theorem tjcosets_orbit_par [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽) ∧
        ∀ i (a : Fin n), (a : ℕ) < j → w i a = 0} := by
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp⟩
    have hp' : (p : GL (Fin n) 𝔽) • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w := hp
    rw [GL_smul_standard_tuple] at hp'
    subst hp'
    refine ⟨GL_columns_linearIndependent n j (p : GL (Fin n) 𝔽), fun i a ha => ?_⟩
    have h0 := (tjcosets_mem_par n j (p : GL (Fin n) 𝔽)).1 p.2 a (tjcosets_idx n j i) ha
      (by simp [tjcosets_idx])
    simpa [Matrix.col] using h0
  · rintro ⟨hw, hz⟩
    obtain ⟨g, hg⟩ := tjcosets_exists_smul n j w hw
    have hg' := hg
    rw [GL_smul_standard_tuple] at hg'
    have hgP : g ∈ tjcosets_par n j := by
      rw [tjcosets_mem_par]
      intro a b ha hb
      have h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a
          = w ⟨b - j, by omega⟩ a := congrFun (congrFun hg' _) a
      rw [tjcosets_idx_sub n j b hb] at h1
      have h2 := h1.trans (hz _ a ha)
      simpa [Matrix.col] using h2
    refine ⟨⟨g, hgP⟩, ?_⟩
    rw [Subgroup.smul_def]
    exact hg

def tjcosets_ext (n j : ℕ) : (Fin (n - j) → 𝔽) →ₗ[𝔽] (Fin n → 𝔽) where
  toFun u a := if h : j ≤ (a : ℕ) then u ⟨a - j, by omega⟩ else 0
  map_add' x y := by funext a; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by funext a; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def tjcosets_pr (n j : ℕ) : (Fin n → 𝔽) →ₗ[𝔽] (Fin (n - j) → 𝔽) where
  toFun x c := x (tjcosets_idx n j c)
  map_add' x y := rfl
  map_smul' c x := rfl

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `[tjcosets_pr, tjcosets_ext, tjcosets_idx]`.
-/
theorem tjcosets_pr_ext (n j : ℕ) (u : Fin (n - j) → 𝔽) :
    tjcosets_pr n j (tjcosets_ext n j u) = u := by
  funext c
  simp [tjcosets_pr, tjcosets_ext, tjcosets_idx]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [tjcosets_pr, tjcosets_ext, LinearMap.coe_mk, AddHom.coe_mk]`. Use `split_ifs with h`. Rewrite using `[tjcosets_idx_sub n j a h]`. Conclude with `(hx a (by omega)).symm`.
-/
theorem tjcosets_ext_pr (n j : ℕ) (x : Fin n → 𝔽) (hx : ∀ a : Fin n, (a : ℕ) < j → x a = 0) :
    tjcosets_ext n j (tjcosets_pr n j x) = x := by
  funext a
  simp only [tjcosets_pr, tjcosets_ext, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · rw [tjcosets_idx_sub n j a h]
  · exact (hx a (by omega)).symm

def tjcosets_equiv (n j : ℕ) :
    {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽) ∧
        ∀ i (a : Fin n), (a : ℕ) < j → w i a = 0} ≃
      {u : Fin (n - j) → Fin (n - j) → 𝔽 // LinearIndependent 𝔽 u} where
  toFun w := ⟨tjcosets_pr n j ∘ w.1, by
    have h : (w.1 : Fin (n - j) → Fin n → 𝔽) = tjcosets_ext n j ∘ (tjcosets_pr n j ∘ w.1) := by
      funext i; exact (tjcosets_ext_pr n j _ (w.2.2 i)).symm
    exact LinearIndependent.of_comp (tjcosets_ext n j) (by rw [← h]; exact w.2.1)⟩
  invFun u := ⟨tjcosets_ext n j ∘ u.1, u.2.map' _ (LinearMap.ker_eq_bot.mpr (fun _ _ h => by
      have := congrArg (tjcosets_pr n j) h
      simpa [tjcosets_pr_ext] using this)), fun i a ha => by
      simp only [Function.comp_apply, tjcosets_ext, LinearMap.coe_mk, AddHom.coe_mk]
      rw [dif_neg (by omega)]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact tjcosets_ext_pr n j _ (w.2.2 i)
  right_inv u := by
    apply Subtype.ext
    funext i
    exact tjcosets_pr_ext n j _

/- English proof (translation)
Establish `hk : n - j ≤ Module.finrank 𝔽 (Fin n → 𝔽)` using `by rw [Module.finrank_fin_fun]; omega`. Establish `hk' : n - j ≤ Module.finrank 𝔽 (Fin (n - j) → 𝔽)` using `by simp`. Establish `cGL : (MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard = ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ))`. Establish `h` using `card_linearIndependent (K := 𝔽) (V := Fin n → 𝔽) hk`. Rewrite `h` using `[Module.finrank_fin_fun]`.

Rewrite using `[tjcosets_orbit_gl, ← Nat.card_coe_set_eq]`. Conclude with `h`. Establish `cP : (MulAction.orbit (tjcosets_par (𝔽` using `𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard = ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) := by`. Establish `h` using `card_linearIndependent (K := 𝔽) (V := Fin (n - j) → 𝔽) hk'`. Rewrite `h` using `[Module.finrank_fin_fun]`.

Rewrite using `[tjcosets_orbit_par, ← Nat.card_coe_set_eq, Nat.card_congr (tjcosets_equiv (𝔽 := 𝔽) n j)]`. Conclude with `h`. Establish `hstab : (MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).relIndex (tjcosets_par n j) = (MulAction.orbit (tjcosets_par (𝔽` using `𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard := by`. Rewrite using `[← MulAction.index_stabilizer, Subgroup.relIndex]`. Use `congr 1`.

Establish `hmul` using `Subgroup.relIndex_mul_index (tjcosets_stab_le_par (𝔽 := 𝔽) n j)`. Rewrite `hmul` using `[MulAction.index_stabilizer, cGL, hstab, cP]`. Rewrite using `[mul_comm]`. Conclude with `hmul`.
-/
theorem tjcosets_ff_count [Fintype 𝔽] (n j : ℕ) (hj : j ≤ n) :
    (tjcosets_par (𝔽 := 𝔽) n j).index *
        ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) := by
  classical
  have hk : n - j ≤ Module.finrank 𝔽 (Fin n → 𝔽) := by rw [Module.finrank_fin_fun]; omega
  have hk' : n - j ≤ Module.finrank 𝔽 (Fin (n - j) → 𝔽) := by simp
  have cGL : (MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) := by
    have h := card_linearIndependent (K := 𝔽) (V := Fin n → 𝔽) hk
    rw [Module.finrank_fin_fun] at h
    rw [tjcosets_orbit_gl, ← Nat.card_coe_set_eq]
    exact h
  have cP : (MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) := by
    have h := card_linearIndependent (K := 𝔽) (V := Fin (n - j) → 𝔽) hk'
    rw [Module.finrank_fin_fun] at h
    rw [tjcosets_orbit_par, ← Nat.card_coe_set_eq, Nat.card_congr (tjcosets_equiv (𝔽 := 𝔽) n j)]
    exact h
  have hstab : (MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).relIndex
      (tjcosets_par n j) =
      (MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
  have hmul := Subgroup.relIndex_mul_index (tjcosets_stab_le_par (𝔽 := 𝔽) n j)
  rw [MulAction.index_stabilizer, cGL, hstab, cP] at hmul
  rw [mul_comm]
  exact hmul

end FF

end Formalism.UG.P
