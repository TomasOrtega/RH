import Mathlib

namespace GlobalTheory.HlCoc

open Topology

def SD (M G : Type) : Type := M × G

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]

def SD.mk (x : M) (g : G) : SD M G := (x, g)

instance : Mul (SD M G) := ⟨fun p q => (p.1 + p.2 • q.1, p.2 * q.2)⟩
instance : One (SD M G) := ⟨((0 : M), (1 : G))⟩
instance : Inv (SD M G) := ⟨fun p => (-(p.2⁻¹ • p.1), p.2⁻¹)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma mul_fst (p q : SD M G) : (p * q).1 = p.1 + p.2 • q.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma mul_snd (p q : SD M G) : (p * q).2 = p.2 * q.2 := rfl
omit [DistribMulAction G M] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma one_fst : (1 : SD M G).1 = 0 := rfl
omit [DistribMulAction G M] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma one_snd : (1 : SD M G).2 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma inv_fst (p : SD M G) : (p⁻¹).1 = -(p.2⁻¹ • p.1) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma inv_snd (p : SD M G) : (p⁻¹).2 = p.2⁻¹ := rfl

instance : Group (SD M G) :=
  Group.ofLeftAxioms
    (fun p q r => Prod.ext (by simp [smul_add, mul_smul, add_assoc]) (by simp [mul_assoc]))
    (fun p => Prod.ext (by simp) (by simp))
    (fun p => Prod.ext (by simp) (by simp))

def sndHom : SD M G →* G where
  toFun p := p.2
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma sndHom_apply (p : SD M G) : sndHom p = p.2 := rfl

/- English proof (translation)
Establish `hs : ∀ k : ℕ, (p ^ k).2 = p.2 ^ k` using `fun k => by`. Simplify using `using map_pow (sndHom : SD M G →* G) p k`. Establish `hf : ∀ k : ℕ, p.2 ^ k • p.1 = p.1`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, mul_smul, h, ih]`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, mul_fst, ih, hs, hf, succ_nsmul]`.
-/
lemma pow_fst_of_fixed (p : SD M G) (h : p.2 • p.1 = p.1) (n : ℕ) :
    (p ^ n).1 = n • p.1 := by
  have hs : ∀ k : ℕ, (p ^ k).2 = p.2 ^ k := fun k => by
    simpa using map_pow (sndHom : SD M G →* G) p k
  have hf : ∀ k : ℕ, p.2 ^ k • p.1 = p.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, h, ih]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_fst, ih, hs, hf, succ_nsmul]

variable [TopologicalSpace G] [TopologicalSpace M]

instance : TopologicalSpace (SD M G) := inferInstanceAs (TopologicalSpace (M × G))

omit [Group G] [AddCommGroup M] [DistribMulAction G M] in
/- English proof (translation)
The claim follows from `continuous_fst`.
-/
lemma cont_fst : Continuous (fun p : SD M G => p.1) := continuous_fst
omit [Group G] [AddCommGroup M] [DistribMulAction G M] in
/- English proof (translation)
The claim follows from `continuous_snd`.
-/
lemma cont_snd : Continuous (fun p : SD M G => p.2) := continuous_snd

instance [T2Space M] [T2Space G] : T2Space (SD M G) := inferInstanceAs (T2Space (M × G))

variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]

instance : IsTopologicalGroup (SD M G) where
  continuous_mul := by
    refine Continuous.prodMk ?_ ?_
    · exact (cont_fst.comp continuous_fst).add
        ((cont_snd.comp continuous_fst).smul (cont_fst.comp continuous_snd))
    · exact (cont_snd.comp continuous_fst).mul (cont_snd.comp continuous_snd)
  continuous_inv := by
    refine Continuous.prodMk ?_ ?_
    · exact (cont_snd.inv.smul cont_fst).neg
    · exact cont_snd.inv

/- English proof (translation)
Establish `hY : IsCompact (⋃ j ∈ Finset.range l, (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E))` using `(Finset.range l).isCompact_biUnion fun j _ => hc.image (continuous_const.mul (continuous_id.pow l))`. Establish `hsub : ((Subgroup.zpowers e : Subgroup E) : Set E) ⊆ ⋃ j ∈ Finset.range l, (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E)`. Introduce `x hx`. Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hx`. Establish `h0 : 0 ≤ n % (l : ℤ)` using `Int.emod_nonneg _ (by exact_mod_cast hl.ne')`.

Establish `h1 : n % (l : ℤ) < l` using `Int.emod_lt_of_pos _ (by exact_mod_cast hl)`. Simplify using `only [Set.mem_iUnion, Set.mem_image, Finset.mem_range]`. Use `⟨(n % l).toNat, by omega, e ^ (n / l), Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers e _), ?_⟩` and prove the remaining obligations. Simplify using `only [← zpow_natCast]`. Rewrite using `[Int.toNat_of_nonneg h0, ← zpow_mul, ← zpow_add, mul_comm, Int.emod_add_mul_ediv]`.

Establish `hmem` using `(closure_minimal hsub hY.isClosed) (by rw [← Subgroup.topologicalClosure_coe]; exact hp)`. Simplify using `only [Set.mem_iUnion, Set.mem_image, Finset.mem_range] at hmem`. Take `⟨j, hj, q, hq, hpq⟩` from `hmem`. Conclude with `⟨j, hj, q, hq, hpq.symm⟩`.
-/
lemma exists_pow_mul_pow {E : Type} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [T2Space E] (e : E) (l : ℕ) (hl : 0 < l)
    (hc : IsCompact ((Subgroup.zpowers e).topologicalClosure : Set E))
    (p : E) (hp : p ∈ (Subgroup.zpowers e).topologicalClosure) :
    ∃ j < l, ∃ q ∈ (Subgroup.zpowers e).topologicalClosure, p = e ^ j * q ^ l := by

  have hY : IsCompact (⋃ j ∈ Finset.range l,
      (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E)) :=
    (Finset.range l).isCompact_biUnion fun j _ =>
      hc.image (continuous_const.mul (continuous_id.pow l))
  have hsub : ((Subgroup.zpowers e : Subgroup E) : Set E) ⊆ ⋃ j ∈ Finset.range l,
      (fun q => e ^ j * q ^ l) '' ((Subgroup.zpowers e).topologicalClosure : Set E) := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h0 : 0 ≤ n % (l : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hl.ne')
    have h1 : n % (l : ℤ) < l := Int.emod_lt_of_pos _ (by exact_mod_cast hl)
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range]
    refine ⟨(n % l).toNat, by omega, e ^ (n / l),
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers e _), ?_⟩
    simp only [← zpow_natCast]
    rw [Int.toNat_of_nonneg h0, ← zpow_mul, ← zpow_add, mul_comm, Int.emod_add_mul_ediv]
  have hmem := (closure_minimal hsub hY.isClosed)
    (by rw [← Subgroup.topologicalClosure_coe]; exact hp)
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range] at hmem
  obtain ⟨j, hj, q, hq, hpq⟩ := hmem
  exact ⟨j, hj, q, hq, hpq.symm⟩

/- English proof (translation)
Establish `hcl : IsClosed (Multiplicative.ofAdd ⁻¹' (f '' S))` using `(hS.image hf).isClosed.preimage continuous_ofAdd`. Establish `hsub : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆ Multiplicative.ofAdd ⁻¹' (f '' S)`. Introduce and unpack `_ ⟨n, rfl⟩`. Take `⟨x, hx, hfx⟩` from `hn n`. Conclude with `⟨x, hx, hfx⟩`.

Establish `hall` using `closure_minimal hsub hcl`. Rewrite `hall` using `[PadicInt.denseRange_natCast.closure_range]`. Take `⟨x, hx, hfx⟩` from `hall (Set.mem_univ (Multiplicative.toAdd a))`. Conclude with `⟨x, hx, hfx⟩`.
-/
private lemma exists_preimage_of_compact_hits_naturals (l : ℕ) [Fact l.Prime] {X : Type} [TopologicalSpace X] (S : Set X)
    (hS : IsCompact S) (f : X → Multiplicative ℤ_[l]) (hf : Continuous f)
    (hn : ∀ n : ℕ, ∃ x ∈ S, f x = Multiplicative.ofAdd (n : ℤ_[l]))
    (a : Multiplicative ℤ_[l]) : ∃ x ∈ S, f x = a := by
  have hcl : IsClosed (Multiplicative.ofAdd ⁻¹' (f '' S)) :=
    (hS.image hf).isClosed.preimage continuous_ofAdd
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆ Multiplicative.ofAdd ⁻¹' (f '' S) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨x, hx, hfx⟩ := hn n
    exact ⟨x, hx, hfx⟩
  have hall := closure_minimal hsub hcl
  rw [PadicInt.denseRange_natCast.closure_range] at hall
  obtain ⟨x, hx, hfx⟩ := hall (Set.mem_univ (Multiplicative.toAdd a))
  exact ⟨x, hx, hfx⟩

/- English proof (translation)
Establish `h1 : c₁ 1 = c₂ 1` using `hH 1 (map_one lam)`. Set `Z : Subgroup G` to `{ carrier := {g | c₁ g = c₂ g} mul_mem' := fun {x y} hx hy => by`. Establish `hx' : c₁ x = c₂ x` using `hx`. Establish `hy' : c₁ y = c₂ y` using `hy`. Use `show c₁ (x * y) = c₂ (x * y)`.

Rewrite using `[co₁, co₂, hx', hy']`. Use the proof step `one_mem' := h1`. Use the proof step `inv_mem' := fun {x} hx => by`. Establish `hx' : c₁ x = c₂ x` using `hx`. Use `show c₁ x⁻¹ = c₂ x⁻¹`.

Establish `e1` using `co₁ x⁻¹ x`. Establish `e2` using `co₂ x⁻¹ x`. Rewrite `e1`, `e2` using `[inv_mul_cancel]`. Rewrite `e1` using `[hx']`. Conclude with `add_right_cancel (e1.symm.trans (h1.trans e2)) }`.

Establish `hZc : IsClosed (Z : Set G)` using `isClosed_eq h₁ h₂`. Establish `hg₀Z : g₀ ∈ Z` using `hg`. Use function extensionality and compare the values at `g`. Take `⟨k, hk, hkl⟩` from `exists_preimage_of_compact_hits_naturals l (Z : Set G) hZc.isCompact lam hlam (fun n => ⟨g₀ ^ n, Z.pow_mem hg₀Z n, by rw [map_pow, hg₀, ← ofAdd_nsmul, nsmul_one]⟩) (lam g)`. Establish `hk' : k⁻¹ * g ∈ Z` using `hH _ (by rw [map_mul, map_inv, hkl, inv_mul_cancel])`.

Use `Z.mul_mem hk hk'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
private lemma cocycle_eq_of_agree_kernel_and_generator (l : ℕ) [Fact l.Prime] [CompactSpace G] [T2Space M]
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (hg₀ : lam g₀ = Multiplicative.ofAdd 1) (c₁ c₂ : G → M)
    (h₁ : Continuous c₁) (h₂ : Continuous c₂)
    (co₁ : ∀ g h, c₁ (g * h) = c₁ g + g • c₁ h) (co₂ : ∀ g h, c₂ (g * h) = c₂ g + g • c₂ h)
    (hH : ∀ h, lam h = 1 → c₁ h = c₂ h) (hg : c₁ g₀ = c₂ g₀) : c₁ = c₂ := by
  have h1 : c₁ 1 = c₂ 1 := hH 1 (map_one lam)
  let Z : Subgroup G :=
    { carrier := {g | c₁ g = c₂ g}
      mul_mem' := fun {x y} hx hy => by
        have hx' : c₁ x = c₂ x := hx
        have hy' : c₁ y = c₂ y := hy
        show c₁ (x * y) = c₂ (x * y)
        rw [co₁, co₂, hx', hy']
      one_mem' := h1
      inv_mem' := fun {x} hx => by
        have hx' : c₁ x = c₂ x := hx
        show c₁ x⁻¹ = c₂ x⁻¹
        have e1 := co₁ x⁻¹ x
        have e2 := co₂ x⁻¹ x
        rw [inv_mul_cancel] at e1 e2
        rw [hx'] at e1
        exact add_right_cancel (e1.symm.trans (h1.trans e2)) }
  have hZc : IsClosed (Z : Set G) := isClosed_eq h₁ h₂
  have hg₀Z : g₀ ∈ Z := hg
  funext g
  obtain ⟨k, hk, hkl⟩ := exists_preimage_of_compact_hits_naturals l (Z : Set G) hZc.isCompact lam hlam
    (fun n => ⟨g₀ ^ n, Z.pow_mem hg₀Z n, by rw [map_pow, hg₀, ← ofAdd_nsmul, nsmul_one]⟩) (lam g)
  have hk' : k⁻¹ * g ∈ Z := hH _ (by rw [map_mul, map_inv, hkl, inv_mul_cancel])
  have := Z.mul_mem hk hk'
  rwa [mul_inv_cancel_left] at this

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Take `⟨e, he1, he2⟩ : ∃ e : SD M G, e.1 = z ∧ e.2 = g₀` from `⟨SD.mk z g₀, rfl, rfl⟩`. Establish `hsn : ∀ (p : SD M G) (n : ℕ), (p ^ n).2 = p.2 ^ n` using `fun p n => by`. Simplify using `using map_pow (sndHom : SD M G →* G) p n`. Set `F : Subgroup (SD M G)` to `{ carrier := {p | ∀ h : G, lam h = 1 → h • p.1 = p.1} mul_mem' := fun {p q} hp hq => by`.

Introduce `h hh`. Establish `hk : lam (p.2⁻¹ * h * p.2) = 1` using `by simp [hh]`. Establish `e1 : h • p.2 • q.1 = p.2 • q.1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul]`.

Use `congr 1`. Use `group`. Use `_ = p.2 • (p.2⁻¹ * h * p.2) • q.1 := mul_smul _ _ _`. Use `_ = p.2 • q.1 := by rw [hq _ hk]`. Rewrite using `[mul_fst, smul_add, hp h hh, e1]`.

Use the proof step `one_mem' := by intro h _; simp`. Use the proof step `inv_mem' := fun {p} hp => by`. Introduce `h hh`. Establish `hk : lam (p.2 * h * p.2⁻¹) = 1` using `by simp [hh]`. Rewrite using `[inv_fst, smul_neg]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul]`. Use `congr 1`. Use `group`.

Use `_ = p.2⁻¹ • (p.2 * h * p.2⁻¹) • p.1 := mul_smul _ _ _`. Use `_ = p.2⁻¹ • p.1 := by rw [hp _ hk] }`. Establish `hFcl : IsClosed (F : Set (SD M G))`. Establish `: (F : Set (SD M G)) = ⋂ h : G, ⋂ (_ : lam h = 1), {p : SD M G | h • p.1 = p.1}`. Use extensionality with `p`.

Simplify using `[F]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun h => isClosed_iInter fun _ => isClosed_eq (continuous_const.smul cont_fst) cont_fst`. Set `W : Subgroup (SD M G)` to `{ carrier := {p | p.1 - (p.2 • b - b) ∈ T} mul_mem' := fun {p q} hp hq => by`. Establish `e1 : (p * q).1 - ((p * q).2 • b - b) = (p.1 - (p.2 • b - b)) + p.2 • (q.1 - (q.2 • b - b))`.

Rewrite using `[mul_fst, mul_snd, smul_sub, smul_sub, mul_smul]`. Normalize the expressions using the abelian group laws. Use `show (p * q).1 - ((p * q).2 • b - b) ∈ T`. Rewrite using `[e1]`. Conclude with `add_mem hp (hTs _ _ hq)`.

Use the proof step `one_mem' := by show (1 : SD M G).1 - ((1 : SD M G).2 • b - b) ∈ T`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := fun {p} hp => by`. Establish `e1 : (p⁻¹).1 - ((p⁻¹).2 • b - b) = -(p.2⁻¹ • (p.1 - (p.2 • b - b)))`. Rewrite using `[inv_fst, inv_snd, smul_sub, smul_sub, smul_smul, inv_mul_cancel, one_smul]`.

Normalize the expressions using the abelian group laws. Use `show (p⁻¹).1 - ((p⁻¹).2 • b - b) ∈ T`. Rewrite using `[e1]`. Conclude with `neg_mem (hTs _ _ hp) }`. Establish `hWc : IsCompact (W : Set (SD M G))`.

Establish `hcont : Continuous (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G))` using `(continuous_fst.add ((continuous_snd.smul continuous_const).sub continuous_const)).prodMk continuous_snd`. Establish `hEq : (W : Set (SD M G)) = (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G)) '' ((T : Set M) ×ˢ (Set.univ : Set G))`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce `hp`.

Use `⟨(p.1 - (p.2 • b - b), p.2), ⟨hp, Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Use `show ((p.1 - (p.2 • b - b) + (p.2 • b - b), p.2) : M × G) = p`. Rewrite using `[sub_add_cancel]`. Both sides reduce to the same expression. Introduce and unpack `⟨x, ⟨hx, -⟩, rfl⟩ show x.1 + (x.2 • b - b) - (x.2 • b - b) ∈ T`.

Rewrite using `[add_sub_cancel_right]`. Conclude with `hx`. Rewrite using `[hEq]`. Conclude with `(hT.prod (isCompact_univ : IsCompact (Set.univ : Set G))).image hcont`. Set `C : Subgroup (SD M G)` to `(Subgroup.zpowers e).topologicalClosure`.

Establish `heC : e ∈ C` using `Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers e)`. Establish `hCF : (C : Set (SD M G)) ⊆ F` using `Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by`. Introduce `h hh`. Use `show h • e.1 = e.1`. Rewrite using `[he1]`.

Conclude with `(hH h hh).1)) hFcl`. Establish `hCW : (C : Set (SD M G)) ⊆ W`. Establish `hW : IsClosed (W : Set (SD M G))` using `hWc.isClosed`. Conclude with `Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by show e.1 - (e.2 • b - b) ∈ T`. Rewrite using `[he1, he2]`.

Conclude with `hz)) hW`. Establish `hCc : IsCompact (C : Set (SD M G))` using `hWc.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) hCW`. Establish `helam : lam e.2 = Multiplicative.ofAdd 1` using `by rw [he2, hg₀]`. Establish `key : ∀ q ∈ C, lam q.2 = 1 → q.1 = 0`. Introduce `q hq hq1`.

Establish `step : ∀ k : ℕ, ∃ r ∈ C, lam r.2 = 1 ∧ q = r ^ (l ^ k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨q, hq, hq1, by rw [pow_zero, pow_one]⟩`. Consider the case `succ k ih`.

Take `⟨r, hr, hr1, hqr⟩` from `ih`. Take `⟨j, hj, s, hs, hrs⟩` from `exists_pow_mul_pow e l hl hCc r hr`. Establish `hlr : lam (e ^ j * s ^ l).2 = 1` using `hrs ▸ hr1`. Rewrite `hlr` using `[mul_snd, hsn, hsn, map_mul, map_pow, map_pow, helam]`. Establish `hadd : (j : ℤ_[l]) + l * Multiplicative.toAdd (lam s.2) = 0`.

Use `congrArg Multiplicative.toAdd hlr` as an intermediate fact. Simplify `this` using `[toAdd_mul, toAdd_pow, nsmul_eq_mul]`. Establish `hjz : (j : ZMod l) = 0`. Use `congrArg (PadicInt.toZMod (p := l)) hadd` as an intermediate fact. Simplify using `using this`.

Establish `hj0 : j = 0` using `Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff j l).mp hjz) hj`. Rewrite `hadd` using `[hj0, Nat.cast_zero, zero_add]`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr hl.ne'`. Establish `hy : Multiplicative.toAdd (lam s.2) = 0` using `(mul_eq_zero.mp hadd).resolve_left hl0`. Use `⟨s, hs, Multiplicative.toAdd.injective (by rw [hy]; rfl), ?_⟩` and prove the remaining obligations.

Rewrite using `[hqr, hrs, hj0, pow_zero, one_mul, ← pow_mul, pow_succ']`. Assume the negation of the conclusion as `hne`. Take `⟨k, hk⟩` from `hTl ({q.1}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))`. Take `⟨r, hr, hr1, hqr⟩` from `step k`. Establish `hfix : r.2 • r.1 = r.1` using `hCF hr r.2 hr1`.

Establish `hrT : r.1 ∈ T`. Establish `h1 : r.1 - (r.2 • b - b) ∈ T` using `hCW hr`. Establish `h2` using `add_mem h1 (hH r.2 hr1).2`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis. Apply `hk r.1 hrT` to reduce the goal to its premises.

Rewrite using `[hqr, pow_fst_of_fixed r hfix]`. Conclude with `Set.mem_singleton _`. Use `choose qq hqC hqlam using exists_preimage_of_compact_hits_naturals l (C : Set (SD M G)) hCc (fun q => lam q.2) (hlam.comp cont_snd) (fun n => ⟨e ^ n, C.pow_mem heC n, by show lam (e ^ n).2 = _`. Rewrite using `[hsn, map_pow, helam, ← ofAdd_nsmul, nsmul_one]⟩)`. Establish `hd : ∀ q ∈ C, (qq (lam q.2)).1 = q.1`.

Introduce `q hq`. Establish `hm : (qq (lam q.2))⁻¹ * q ∈ C` using `C.mul_mem (C.inv_mem (hqC _)) hq`. Establish `h1 : lam ((qq (lam q.2))⁻¹ * q).2 = 1`. Rewrite using `[mul_snd, inv_snd, map_mul, map_inv, hqlam, inv_mul_cancel]`. Establish `h0` using `key _ hm h1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0, smul_zero, add_zero]`. Use `_ = (qq (lam q.2) * ((qq (lam q.2))⁻¹ * q)).1 := (mul_fst _ _).symm`. Use `_ = q.1 := by rw [mul_inv_cancel_left]`. Establish `hdc : Continuous (fun a => (qq a).1)`.

Rewrite using `[continuous_iff_isClosed]`. Introduce `K hK`. Establish `hcl : IsClosed ((fun q : SD M G => lam q.2) '' ((C : Set (SD M G)) ∩ (fun q : SD M G => q.1) ⁻¹' K))` using `((hCc.inter_right (hK.preimage cont_fst)).image (hlam.comp cont_snd)).isClosed`. Use `hcl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨qq a, ⟨hqC a, ha⟩, hqlam a⟩`. Introduce and unpack `⟨q, ⟨hq, hqK⟩, rfl⟩ show (qq (lam q.2)).1 ∈ K`. Rewrite using `[hd q hq]`.

Conclude with `hqK`. Take `⟨c, hcdef⟩ : ∃ c : G → M, ∀ g, c g = (qq (lam g)).1 - (g • b - b)` from `⟨_, fun _ => rfl⟩`. Establish `cc : Continuous c`. Rewrite using `[show c = fun g => (qq (lam g)).1 - (g • b - b) from funext hcdef]`. Conclude with `(hdc.comp hlam).sub ((continuous_id.smul continuous_const).sub continuous_const)`.

Establish `cT : ∀ g, c g ∈ T`. Introduce `g`. Establish `hq : (qq (lam g)).1 - ((qq (lam g)).2 • b - b) ∈ T` using `hCW (hqC (lam g))`. Establish `hk : lam ((qq (lam g)).2⁻¹ * g) = 1`. Rewrite using `[map_mul, map_inv, hqlam, inv_mul_cancel]`.

Establish `hT2` using `hTs (qq (lam g)).2 _ (hH _ hk).2`. Establish `e1 : (qq (lam g)).1 - (g • b - b) = ((qq (lam g)).1 - ((qq (lam g)).2 • b - b)) - (qq (lam g)).2 • (((qq (lam g)).2⁻¹ * g) • b - b)`. Rewrite using `[smul_sub, smul_smul, mul_inv_cancel_left]`. Normalize the expressions using the abelian group laws. Rewrite using `[hcdef, e1]`.

Conclude with `sub_mem hq hT2`. Establish `cco : ∀ g h, c (g * h) = c g + g • c h`. Introduce `g h`. Establish `hm` using `C.mul_mem (hqC (lam g)) (hqC (lam h))`. Establish `hl2 : lam (qq (lam g) * qq (lam h)).2 = lam (g * h)`.

Rewrite using `[mul_snd, map_mul, hqlam, hqlam, map_mul]`. Establish `h1` using `hd _ hm`. Rewrite `h1` using `[hl2, mul_fst]`. Establish `hk : lam ((qq (lam g)).2⁻¹ * g) = 1`. Rewrite using `[map_mul, map_inv, hqlam, inv_mul_cancel]`.

Establish `hfx : g • (qq (lam h)).1 = (qq (lam g)).2 • (qq (lam h)).1` using `by conv_lhs => rw [← mul_inv_cancel_left (qq (lam g)).2 g]`. Rewrite using `[mul_smul, hCF (hqC (lam h)) _ hk]`. Rewrite using `[hcdef, hcdef, hcdef, h1, smul_sub, smul_sub, hfx, mul_smul]`. Normalize the expressions using the abelian group laws. Establish `cH : ∀ h, lam h = 1 → c h = -(h • b - b)`.

Introduce `h hh`. Establish `h0` using `hd 1 C.one_mem`. Rewrite `h0` using `[one_snd, map_one, one_fst]`. Rewrite using `[hcdef, hh, h0, zero_sub]`. Establish `cg : ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b)`.

Introduce `g hg`. Establish `h0` using `hd e heC`. Rewrite `h0` using `[helam, he1]`. Rewrite using `[hcdef, hg, h0]`. Use `⟨c, ⟨cc, cT, cco, cH, cg⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `c₂ ⟨hc₂, -, hco₂, hH₂, hg₂⟩`. Conclude with `cocycle_eq_of_agree_kernel_and_generator l lam hlam g₀ hg₀ c₂ c hc₂ cc hco₂ cco (fun h hh => by rw [hH₂ h hh, cH h hh]) (by rw [hg₂ g₀ hg₀, cg g₀ hg₀])`.
-/
theorem main (l : ℕ) [Fact l.Prime] [CompactSpace G] [T2Space G] [T2Space M]
    (T : AddSubgroup M) (hT : IsCompact (T : Set M)) (hTs : ∀ g : G, ∀ t ∈ T, g • t ∈ T)
    (hTl : ∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U)
    (lam : G →* Multiplicative ℤ_[l]) (g₀ : G) (hlam : Continuous lam)
    (hg₀ : lam g₀ = Multiplicative.ofAdd 1) (b z : M)
    (hH : ∀ h, lam h = 1 → h • z = z ∧ h • b - b ∈ T) (hz : z - (g₀ • b - b) ∈ T) :
    ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + g • c h) ∧
      (∀ h, lam h = 1 → c h = -(h • b - b)) ∧
      ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b) := by
  classical
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨e, he1, he2⟩ : ∃ e : SD M G, e.1 = z ∧ e.2 = g₀ := ⟨SD.mk z g₀, rfl, rfl⟩
  have hsn : ∀ (p : SD M G) (n : ℕ), (p ^ n).2 = p.2 ^ n := fun p n => by
    simpa using map_pow (sndHom : SD M G →* G) p n

  let F : Subgroup (SD M G) :=
    { carrier := {p | ∀ h : G, lam h = 1 → h • p.1 = p.1}
      mul_mem' := fun {p q} hp hq => by
        intro h hh
        have hk : lam (p.2⁻¹ * h * p.2) = 1 := by simp [hh]
        have e1 : h • p.2 • q.1 = p.2 • q.1 := by
          calc h • p.2 • q.1 = (p.2 * (p.2⁻¹ * h * p.2)) • q.1 := by
                rw [smul_smul]; congr 1; group
            _ = p.2 • (p.2⁻¹ * h * p.2) • q.1 := mul_smul _ _ _
            _ = p.2 • q.1 := by rw [hq _ hk]
        rw [mul_fst, smul_add, hp h hh, e1]
      one_mem' := by intro h _; simp
      inv_mem' := fun {p} hp => by
        intro h hh
        have hk : lam (p.2 * h * p.2⁻¹) = 1 := by simp [hh]
        rw [inv_fst, smul_neg]
        congr 1
        calc h • p.2⁻¹ • p.1 = (p.2⁻¹ * (p.2 * h * p.2⁻¹)) • p.1 := by
              rw [smul_smul]; congr 1; group
          _ = p.2⁻¹ • (p.2 * h * p.2⁻¹) • p.1 := mul_smul _ _ _
          _ = p.2⁻¹ • p.1 := by rw [hp _ hk] }
  have hFcl : IsClosed (F : Set (SD M G)) := by
    have : (F : Set (SD M G)) = ⋂ h : G, ⋂ (_ : lam h = 1), {p : SD M G | h • p.1 = p.1} := by
      ext p; simp [F]
    rw [this]
    exact isClosed_iInter fun h => isClosed_iInter fun _ =>
      isClosed_eq (continuous_const.smul cont_fst) cont_fst

  let W : Subgroup (SD M G) :=
    { carrier := {p | p.1 - (p.2 • b - b) ∈ T}
      mul_mem' := fun {p q} hp hq => by
        have e1 : (p * q).1 - ((p * q).2 • b - b) =
            (p.1 - (p.2 • b - b)) + p.2 • (q.1 - (q.2 • b - b)) := by
          rw [mul_fst, mul_snd, smul_sub, smul_sub, mul_smul]; abel
        show (p * q).1 - ((p * q).2 • b - b) ∈ T
        rw [e1]
        exact add_mem hp (hTs _ _ hq)
      one_mem' := by
        show (1 : SD M G).1 - ((1 : SD M G).2 • b - b) ∈ T
        simp
      inv_mem' := fun {p} hp => by
        have e1 : (p⁻¹).1 - ((p⁻¹).2 • b - b) = -(p.2⁻¹ • (p.1 - (p.2 • b - b))) := by
          rw [inv_fst, inv_snd, smul_sub, smul_sub, smul_smul, inv_mul_cancel, one_smul]; abel
        show (p⁻¹).1 - ((p⁻¹).2 • b - b) ∈ T
        rw [e1]
        exact neg_mem (hTs _ _ hp) }
  have hWc : IsCompact (W : Set (SD M G)) := by
    have hcont : Continuous (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G)) :=
      (continuous_fst.add ((continuous_snd.smul continuous_const).sub continuous_const)).prodMk
        continuous_snd
    have hEq : (W : Set (SD M G)) = (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G)) ''
        ((T : Set M) ×ˢ (Set.univ : Set G)) := by
      ext p
      constructor
      · intro hp
        refine ⟨(p.1 - (p.2 • b - b), p.2), ⟨hp, Set.mem_univ _⟩, ?_⟩
        show ((p.1 - (p.2 • b - b) + (p.2 • b - b), p.2) : M × G) = p
        rw [sub_add_cancel]
        rfl
      · rintro ⟨x, ⟨hx, -⟩, rfl⟩
        show x.1 + (x.2 • b - b) - (x.2 • b - b) ∈ T
        rw [add_sub_cancel_right]
        exact hx
    rw [hEq]
    exact (hT.prod (isCompact_univ : IsCompact (Set.univ : Set G))).image hcont

  let C : Subgroup (SD M G) := (Subgroup.zpowers e).topologicalClosure
  have heC : e ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers e)
  have hCF : (C : Set (SD M G)) ⊆ F :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by
      intro h hh
      show h • e.1 = e.1
      rw [he1]; exact (hH h hh).1)) hFcl
  have hCW : (C : Set (SD M G)) ⊆ W := by
    have hW : IsClosed (W : Set (SD M G)) := hWc.isClosed
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by
      show e.1 - (e.2 • b - b) ∈ T
      rw [he1, he2]; exact hz)) hW
  have hCc : IsCompact (C : Set (SD M G)) :=
    hWc.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) hCW
  have helam : lam e.2 = Multiplicative.ofAdd 1 := by rw [he2, hg₀]

  have key : ∀ q ∈ C, lam q.2 = 1 → q.1 = 0 := by
    intro q hq hq1
    have step : ∀ k : ℕ, ∃ r ∈ C, lam r.2 = 1 ∧ q = r ^ (l ^ k) := by
      intro k
      induction k with
      | zero => exact ⟨q, hq, hq1, by rw [pow_zero, pow_one]⟩
      | succ k ih =>
        obtain ⟨r, hr, hr1, hqr⟩ := ih
        obtain ⟨j, hj, s, hs, hrs⟩ := exists_pow_mul_pow e l hl hCc r hr
        have hlr : lam (e ^ j * s ^ l).2 = 1 := hrs ▸ hr1
        rw [mul_snd, hsn, hsn, map_mul, map_pow, map_pow, helam] at hlr
        have hadd : (j : ℤ_[l]) + l * Multiplicative.toAdd (lam s.2) = 0 := by
          have := congrArg Multiplicative.toAdd hlr
          simpa [toAdd_mul, toAdd_pow, nsmul_eq_mul] using this
        have hjz : (j : ZMod l) = 0 := by
          have := congrArg (PadicInt.toZMod (p := l)) hadd
          simpa using this
        have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff j l).mp hjz) hj
        rw [hj0, Nat.cast_zero, zero_add] at hadd
        have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
        have hy : Multiplicative.toAdd (lam s.2) = 0 := (mul_eq_zero.mp hadd).resolve_left hl0
        refine ⟨s, hs, Multiplicative.toAdd.injective (by rw [hy]; rfl), ?_⟩
        rw [hqr, hrs, hj0, pow_zero, one_mul, ← pow_mul, pow_succ']
    by_contra hne
    obtain ⟨k, hk⟩ := hTl ({q.1}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    obtain ⟨r, hr, hr1, hqr⟩ := step k
    have hfix : r.2 • r.1 = r.1 := hCF hr r.2 hr1
    have hrT : r.1 ∈ T := by
      have h1 : r.1 - (r.2 • b - b) ∈ T := hCW hr
      have h2 := add_mem h1 (hH r.2 hr1).2
      rwa [sub_add_cancel] at h2
    apply hk r.1 hrT
    rw [hqr, pow_fst_of_fixed r hfix]
    exact Set.mem_singleton _

  choose qq hqC hqlam using exists_preimage_of_compact_hits_naturals l (C : Set (SD M G)) hCc (fun q => lam q.2)
    (hlam.comp cont_snd) (fun n => ⟨e ^ n, C.pow_mem heC n, by
      show lam (e ^ n).2 = _
      rw [hsn, map_pow, helam, ← ofAdd_nsmul, nsmul_one]⟩)

  have hd : ∀ q ∈ C, (qq (lam q.2)).1 = q.1 := by
    intro q hq
    have hm : (qq (lam q.2))⁻¹ * q ∈ C := C.mul_mem (C.inv_mem (hqC _)) hq
    have h1 : lam ((qq (lam q.2))⁻¹ * q).2 = 1 := by
      rw [mul_snd, inv_snd, map_mul, map_inv, hqlam, inv_mul_cancel]
    have h0 := key _ hm h1
    calc (qq (lam q.2)).1
        = (qq (lam q.2)).1 + (qq (lam q.2)).2 • ((qq (lam q.2))⁻¹ * q).1 := by
          rw [h0, smul_zero, add_zero]
      _ = (qq (lam q.2) * ((qq (lam q.2))⁻¹ * q)).1 := (mul_fst _ _).symm
      _ = q.1 := by rw [mul_inv_cancel_left]
  have hdc : Continuous (fun a => (qq a).1) := by
    rw [continuous_iff_isClosed]
    intro K hK
    have hcl : IsClosed ((fun q : SD M G => lam q.2) ''
        ((C : Set (SD M G)) ∩ (fun q : SD M G => q.1) ⁻¹' K)) :=
      ((hCc.inter_right (hK.preimage cont_fst)).image (hlam.comp cont_snd)).isClosed
    convert hcl using 1
    ext a
    constructor
    · intro ha
      exact ⟨qq a, ⟨hqC a, ha⟩, hqlam a⟩
    · rintro ⟨q, ⟨hq, hqK⟩, rfl⟩
      show (qq (lam q.2)).1 ∈ K
      rw [hd q hq]; exact hqK
  obtain ⟨c, hcdef⟩ : ∃ c : G → M, ∀ g, c g = (qq (lam g)).1 - (g • b - b) :=
    ⟨_, fun _ => rfl⟩
  have cc : Continuous c := by
    rw [show c = fun g => (qq (lam g)).1 - (g • b - b) from funext hcdef]
    exact (hdc.comp hlam).sub ((continuous_id.smul continuous_const).sub continuous_const)
  have cT : ∀ g, c g ∈ T := by
    intro g
    have hq : (qq (lam g)).1 - ((qq (lam g)).2 • b - b) ∈ T := hCW (hqC (lam g))
    have hk : lam ((qq (lam g)).2⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hqlam, inv_mul_cancel]
    have hT2 := hTs (qq (lam g)).2 _ (hH _ hk).2
    have e1 : (qq (lam g)).1 - (g • b - b) = ((qq (lam g)).1 - ((qq (lam g)).2 • b - b)) -
        (qq (lam g)).2 • (((qq (lam g)).2⁻¹ * g) • b - b) := by
      rw [smul_sub, smul_smul, mul_inv_cancel_left]; abel
    rw [hcdef, e1]
    exact sub_mem hq hT2
  have cco : ∀ g h, c (g * h) = c g + g • c h := by
    intro g h
    have hm := C.mul_mem (hqC (lam g)) (hqC (lam h))
    have hl2 : lam (qq (lam g) * qq (lam h)).2 = lam (g * h) := by
      rw [mul_snd, map_mul, hqlam, hqlam, map_mul]
    have h1 := hd _ hm
    rw [hl2, mul_fst] at h1
    have hk : lam ((qq (lam g)).2⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hqlam, inv_mul_cancel]
    have hfx : g • (qq (lam h)).1 = (qq (lam g)).2 • (qq (lam h)).1 := by
      conv_lhs => rw [← mul_inv_cancel_left (qq (lam g)).2 g]
      rw [mul_smul, hCF (hqC (lam h)) _ hk]
    rw [hcdef, hcdef, hcdef, h1, smul_sub, smul_sub, hfx, mul_smul]; abel
  have cH : ∀ h, lam h = 1 → c h = -(h • b - b) := by
    intro h hh
    have h0 := hd 1 C.one_mem
    rw [one_snd, map_one, one_fst] at h0
    rw [hcdef, hh, h0, zero_sub]
  have cg : ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b) := by
    intro g hg
    have h0 := hd e heC
    rw [helam, he1] at h0
    rw [hcdef, hg, h0]
  refine ⟨c, ⟨cc, cT, cco, cH, cg⟩, ?_⟩
  rintro c₂ ⟨hc₂, -, hco₂, hH₂, hg₂⟩
  exact cocycle_eq_of_agree_kernel_and_generator l lam hlam g₀ hg₀ c₂ c hc₂ cc hco₂ cco
    (fun h hh => by rw [hH₂ h hh, cH h hh]) (by rw [hg₂ g₀ hg₀, cg g₀ hg₀])

/- English proof (translation)
Introduce `l _ G M _ _ _ _ _ _ _ _ _ _ a ha1 ham hac T hT hTs hTl lam g₀ hlam hg₀ b z hH hz`. Set `_ : DistribMulAction G M` to `{ smul := fun g x => a g x one_smul := ha1 mul_smul := ham smul_zero := fun g => map_zero (a g) smul_add := fun g => map_add (a g) }`. Establish `: ContinuousSMul G M` using `⟨hac⟩`. Conclude with `main l T hT hTs hTl lam g₀ hlam hg₀ b z hH hz`.
-/
theorem exists_unique_cocycle : ∀ (l : ℕ) [Fact l.Prime] (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] (a : G → (M →+ M)), (∀ x, a 1 x = x) → (∀ g h x, a (g * h) x = a g (a h x)) → Continuous (fun p : G × M => a p.1 p.2) → ∀ T : AddSubgroup M, IsCompact (T : Set M) → (∀ g, ∀ t ∈ T, a g t ∈ T) → (∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U) → ∀ (lam : G →* Multiplicative ℤ_[l]) (g₀ : G), Continuous lam → lam g₀ = Multiplicative.ofAdd 1 → ∀ b z : M, (∀ h, lam h = 1 → a h z = z ∧ a h b - b ∈ T) → z - (a g₀ b - b) ∈ T → ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + a g (c h)) ∧ (∀ h, lam h = 1 → c h = -(a h b - b)) ∧ ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (a g b - b) := by
  intro l _ G M _ _ _ _ _ _ _ _ _ _ a ha1 ham hac T hT hTs hTl lam g₀ hlam hg₀ b z hH hz
  let _ : DistribMulAction G M :=
    { smul := fun g x => a g x
      one_smul := ha1
      mul_smul := ham
      smul_zero := fun g => map_zero (a g)
      smul_add := fun g => map_add (a g) }
  have : ContinuousSMul G M := ⟨hac⟩
  exact main l T hT hTs hTl lam g₀ hlam hg₀ b z hH hz

end GlobalTheory.HlCoc
