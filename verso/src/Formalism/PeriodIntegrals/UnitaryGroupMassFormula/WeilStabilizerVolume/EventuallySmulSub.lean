import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.MeasureEqOfCos

noncomputable section

namespace PI.VolStabW

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribMulAction.toAddMonoidHom W t)

omit [TopologicalSpace K] in
/- English proof (translation)
Simplify using `[smulSub, AddSubgroup.mem_map]`.
-/
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp [smulSub, AddSubgroup.mem_map]

/- English proof (translation)
Use extensionality with `z`. Simplify using `[smulSub, AddSubgroup.coe_map]`.
-/
theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  simp [smulSub, AddSubgroup.coe_map]

/- English proof (translation)
Rewrite using `[coe_smulSub]`. Conclude with `(Homeomorph.smulOfNeZero t ht).isOpenMap _ hP`.
-/
theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact (Homeomorph.smulOfNeZero t ht).isOpenMap _ hP

/- English proof (translation)
Rewrite using `[coe_smulSub]`. Conclude with `hP.image (continuous_const_smul t)`.
-/
theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact hP.image (continuous_const_smul t)

/- English proof (translation)
Establish `hP : ∀ p ∈ S, ∀ᶠ q : K × W in 𝓝 ((0 : K), p), q.1 • q.2 ∈ N`. Introduce `p _`. Establish `h : Tendsto (fun q : K × W => q.1 • q.2) (𝓝 ((0 : K), p)) (𝓝 (0 : W))`. Simplify using `using (continuous_smul : Continuous fun q : K × W => q.1 • q.2).tendsto ((0 : K), p)`. Conclude with `h hN`.

Establish `hev` using `hS.eventually_forall_of_forall_eventually (P := fun (t : K) (p : W) => t • p ∈ N) hP`. Conclude with `(hs.eventually hev).exists`.
-/
theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hP : ∀ p ∈ S, ∀ᶠ q : K × W in 𝓝 ((0 : K), p), q.1 • q.2 ∈ N := by
    intro p _
    have h : Tendsto (fun q : K × W => q.1 • q.2) (𝓝 ((0 : K), p)) (𝓝 (0 : W)) := by
      simpa using (continuous_smul : Continuous fun q : K × W => q.1 • q.2).tendsto ((0 : K), p)
    exact h hN
  have hev := hS.eventually_forall_of_forall_eventually (P := fun (t : K) (p : W) => t • p ∈ N) hP
  exact (hs.eventually hev).exists

variable [T2Space X]

/- English proof (translation)
Establish `hπkL : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro w hw`. Simplify using `using hw`.

Consider the case `succ k ih`. Introduce `w hw`. Rewrite using `[pow_succ, mul_smul]`. Conclude with `ih _ (hπL w hw)`. Establish `hstep : ∀ k : ℕ, ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub (π ^ k) P`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `p hp`. Conclude with `⟨0, L.zero_mem, (mem_smulSub _ _ _).2 ⟨p, hp, by simp⟩⟩`.

Consider the case `succ k ih`. Introduce `p hp`. Take `⟨l, hl, hpl⟩` from `ih p hp`. Take `⟨p', hp', e1⟩` from `(mem_smulSub _ _ _).1 hpl`. Take `⟨l', hl', hpl'⟩` from `hbase p' hp'`.

Take `⟨p'', hp'', e2⟩` from `(mem_smulSub _ _ _).1 hpl'`. Use `⟨l + π ^ k • l', L.add_mem hl (hπkL k l' hl'), (mem_smulSub _ _ _).2 ⟨p'', hp'', ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_add, hDs, pow_succ, mul_smul, e2, smul_sub, e1]`. Normalize the expressions using the abelian group laws. Use `set S : Set X := D '' (L : Set V) with hS`.

Establish `hSc : IsClosed S` using `(hLc.image hDc).isClosed`. Establish `hb : ∀ N ∈ 𝓝 (0 : X), ∃ k, (smulSub (π ^ k) P : Set X) ⊆ N`. Introduce `N hN`. Take `⟨k, hk⟩` from `eventually_smul_sub (P : Set X) hPc (fun k => π ^ k) hπ N hN`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[coe_smulSub]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `hk p hp`. Introduce `p hp`. Establish `hmem : p ∈ ⋂ k, thick S (smulSub (π ^ k) P)`.

Use `mem_iInter.2 fun k => ?_` and prove the remaining obligations. Take `⟨l, hl, hpl⟩` from `hstep k p hp`. Conclude with `⟨D l, ⟨l, hl, rfl⟩, hpl⟩`. Rewrite `hmem` using `[iInter_thick S hSc (fun k => smulSub (π ^ k) P) hb]`. Take `⟨l, hl, e⟩` from `hmem`.

Conclude with `⟨l, hl, e⟩`.
-/
theorem reach_of_approx (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  have hπkL : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ, mul_smul]
      exact ih _ (hπL w hw)
  have hstep : ∀ k : ℕ, ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub (π ^ k) P := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact ⟨0, L.zero_mem, (mem_smulSub _ _ _).2 ⟨p, hp, by simp⟩⟩
    | succ k ih =>
      intro p hp
      obtain ⟨l, hl, hpl⟩ := ih p hp
      obtain ⟨p', hp', e1⟩ := (mem_smulSub _ _ _).1 hpl
      obtain ⟨l', hl', hpl'⟩ := hbase p' hp'
      obtain ⟨p'', hp'', e2⟩ := (mem_smulSub _ _ _).1 hpl'
      refine ⟨l + π ^ k • l', L.add_mem hl (hπkL k l' hl'), (mem_smulSub _ _ _).2 ⟨p'', hp'', ?_⟩⟩
      rw [map_add, hDs, pow_succ, mul_smul, e2, smul_sub, e1]
      abel
  set S : Set X := D '' (L : Set V) with hS
  have hSc : IsClosed S := (hLc.image hDc).isClosed
  have hb : ∀ N ∈ 𝓝 (0 : X), ∃ k, (smulSub (π ^ k) P : Set X) ⊆ N := by
    intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (P : Set X) hPc (fun k => π ^ k) hπ N hN
    refine ⟨k, ?_⟩
    rw [coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp
  intro p hp
  have hmem : p ∈ ⋂ k, thick S (smulSub (π ^ k) P) := by
    refine mem_iInter.2 fun k => ?_
    obtain ⟨l, hl, hpl⟩ := hstep k p hp
    exact ⟨D l, ⟨l, hl, rfl⟩, hpl⟩
  rw [iInter_thick S hSc (fun k => smulSub (π ^ k) P) hb] at hmem
  obtain ⟨l, hl, e⟩ := hmem
  exact ⟨l, hl, e⟩

/- English proof (translation)
Establish `hβ0 : ∀ w, β 0 w = 0` using `fun w => by`. Establish `h` using `hβ1 0 0 w`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Establish `hβ0' : ∀ u, β u 0 = 0` using `fun u => by`.

Establish `h` using `hβ2 u 0 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Set `Dm : V → V →+ X` to `fun u => { toFun := β u, map_zero' := hβ0' u, map_add' := hβ2 u }`. Establish `hDm : ∀ u w, Dm u w = β u w` using `fun _ _ => rfl`.

Establish `hDmc : ∀ u, Continuous (Dm u)` using `fun u => hβc.comp (Continuous.prodMk continuous_const continuous_id)`. Use `set P : AddSubgroup X := L.map (Dm x) with hPdef`. Establish `hPset : (P : Set X) = β x '' (L : Set V)`. Rewrite using `[hPdef, AddSubgroup.coe_map]`. Both sides reduce to the same expression.

Establish `hPo : IsOpen (P : Set X)` using `by rw [hPset]; exact hxo`. Establish `hPc : IsCompact (P : Set X)` using `by rw [hPset]; exact hLc.image (hDmc x)`. Establish `hπP : ∀ p ∈ P, π • p ∈ P`. Introduce `p hp`. Take `⟨l, hl, rfl⟩` from `AddSubgroup.mem_map.1 hp`.

Conclude with `AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, by rw [hDm, hDm, hβs]⟩`. Establish `hπkP : ∀ k : ℕ, ∀ p ∈ P, π ^ k • p ∈ P`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro p hp`.

Simplify using `using hp`. Consider the case `succ k ih`. Introduce `p hp`. Rewrite using `[pow_succ, mul_smul]`. Conclude with `ih _ (hπP p hp)`.

Use `set πP := smulSub π P with hπPdef`. Establish `hπPo : IsOpen (πP : Set X)` using `isOpen_smulSub π hπ0 P hPo`. Establish `hN1 : ∀ᶠ u in 𝓝 (0 : V), ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)`. Establish `hP : ∀ w ∈ (L : Set V), ∀ᶠ q : V × V in 𝓝 ((0 : V), w), β q.1 q.2 ∈ (πP : Set X)`. Introduce `w _`.

Establish `h` using `hβc.tendsto ((0 : V), w)`. Establish `hm : β ((0 : V), w).1 ((0 : V), w).2 ∈ (πP : Set X)` using `by show β 0 w ∈ (πP : Set X)`. Rewrite using `[hβ0]`. Conclude with `πP.zero_mem`. Conclude with `h (hπPo.mem_nhds hm)`.

Conclude with `hLc.eventually_forall_of_forall_eventually (P := fun (u : V) (w : V) => β u w ∈ (πP : Set X)) hP`. Take `⟨N2, hN2, hsm⟩` from `hsmall πP (hπPo.mem_nhds πP.zero_mem)`. Use `⟨{u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2, inter_mem hN1 hN2, ?_⟩` and prove the remaining obligations. Introduce and unpack `y hy Λ0 ⟨c, hc0, rfl⟩ hsub`. Establish `hcL : ∀ w ∈ L, c • w ∈ {u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2` using `fun w hw => hsub (AddSubgroup.mem_map.2 ⟨w, hw, rfl⟩)`.

Establish `hcG : ∀ w ∈ L, c • G w ∈ πP` using `hsm c (fun w hw => (hcL w hw).2)`. Establish `hreach : ∀ p ∈ P, ∃ l ∈ L, Dm y l = p`. Use `reach_of_approx π hπ L hLc hπL (Dm y) (hDmc y) (fun t w => hβs t y w) P hPc ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨l, hl, rfl⟩` from `AddSubgroup.mem_map.1 hp`.

Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Establish `e : Dm x l - Dm y l = -(β (y - x) l)`. Rewrite using `[hDm, hDm]`. Use `hβ1 x (y - x) l` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`.

Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `πP.neg_mem (hy.1 l hl)`. Use `set Q := L.map (Dm y) with hQdef`.

Establish `hPQ : P ≤ Q` using `fun p hp => by`. Take `⟨l, hl, e⟩` from `hreach p hp`. Conclude with `AddSubgroup.mem_map.2 ⟨l, hl, e⟩`. Establish `hQo : IsOpen (Q : Set X)` using `AddSubgroup.isOpen_mono hPQ hPo`. Establish `hQc : IsCompact (Q : Set X)` using `by rw [hQdef, AddSubgroup.coe_map]; exact hLc.image (hDmc y)`.

Use `set s : ℕ → K := fun n => π ^ n * c with hsdef`. Establish `hs0 : ∀ n, s n ≠ 0` using `fun n => mul_ne_zero (pow_ne_zero n hπ0) hc0`. Establish `hsc : s 0 = c` using `by simp [hsdef]`. Use `set Λ : ℕ → AddSubgroup V := fun n => smulSub (s n) L with hΛdef`. Establish `hH : ∀ n, (Λ n).map (Dm y) = smulSub (s n) Q`.

Introduce `n`. Use extensionality with `z`. Rewrite using `[AddSubgroup.mem_map, mem_smulSub]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Take `⟨l, hl, rfl⟩` from `(mem_smulSub _ _ _).1 hv`. Conclude with `⟨Dm y l, AddSubgroup.mem_map_of_mem _ hl, by rw [hDm, hDm, hβs]⟩`. Introduce and unpack `⟨q, hq, rfl⟩`. Take `⟨l, hl, rfl⟩` from `AddSubgroup.mem_map.1 hq`. Conclude with `⟨s n • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, by rw [hDm, hDm, hβs]⟩`.

Use `⟨Λ, fun n => (Λ n).map (Dm y), Dm y, ?_, fun n => isOpen_smulSub _ (hs0 n) L hLo, fun n => isCompact_smulSub _ L hLc, ?_, ?_, ?_, ?_, fun n => rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [hΛdef, smulSub, hsc]`. Use `antitone_nat_of_succ_le fun n z hz => ?_` and prove the remaining obligations. Take `⟨l, hl, rfl⟩` from `(mem_smulSub _ _ _).1 hz`. Use `(mem_smulSub _ _ _).2 ⟨π • l, hπL l hl, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [hsdef]`. Expand and normalize the polynomial expressions, which then agree. Introduce `n show IsOpen (((Λ n).map (Dm y) : AddSubgroup X) : Set X)`.

Rewrite using `[hH]`. Conclude with `isOpen_smulSub _ (hs0 n) Q hQo`. Introduce `n show IsCompact (((Λ n).map (Dm y) : AddSubgroup X) : Set X)`. Rewrite using `[hH]`. Conclude with `isCompact_smulSub _ Q hQc`.

Introduce `N' hN'`. Establish `hst : Tendsto s atTop (𝓝 0)`. Use `hπ.mul_const c` as an intermediate fact. Simplify `this` using `[hsdef]`. Take `⟨k, hk⟩` from `eventually_smul_sub (Q : Set X) hQc s hst N' hN'`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show (((Λ k).map (Dm y) : AddSubgroup X) : Set X) ⊆ N'`. Rewrite using `[hH, coe_smulSub]`. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `hk q hq`.

Introduce `n Z hZ W hW`. Take `⟨z, hz, rfl⟩` from `(mem_smulSub _ _ _).1 hZ`. Take `⟨w, hw, rfl⟩` from `(mem_smulSub _ _ _).1 hW`. Rewrite using `[hsc]`. Use `show G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) ∈ (Λ (n + 1)).map (Dm y)`.

Establish `e1 : G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) = β (c • z) (s n • w) + G (s n • w)`. Rewrite using `[hG (y + c • z) (s n • w), hβ1 y (c • z)]`. Normalize the expressions using the abelian group laws. Take `⟨p1, hp1, e2⟩` from `(mem_smulSub _ _ _).1 ((hcL z hz).1 w hw)`. Take `⟨p2, hp2, e3⟩` from `(mem_smulSub _ _ _).1 (hcG w hw)`.

Establish `e4 : β (c • z) (s n • w) + G (s n • w) = s (n + 1) • (p1 + π ^ n • p2)`. Rewrite using `[hβs, hGs, ← e2]`. Establish `e5 : s n • s n • G w = s n • π ^ n • (c • G w)`. Simplify using `only [hsdef]`. Use `module`.

Rewrite using `[e5, ← e3]`. Simplify using `only [hsdef]`. Use `module`. Rewrite using `[e1, e4, hH]`. Conclude with `(mem_smulSub _ _ _).2 ⟨_, hPQ (P.add_mem hp1 (hπkP n p2 hp2)), rfl⟩`.
-/
theorem filt_abstract [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribMulAction.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) := by
  have hβ0 : ∀ w, β 0 w = 0 := fun w => by
    have h := hβ1 0 0 w
    rw [add_zero] at h
    simpa using h
  have hβ0' : ∀ u, β u 0 = 0 := fun u => by
    have h := hβ2 u 0 0
    rw [add_zero] at h
    simpa using h
  let Dm : V → V →+ X := fun u =>
    { toFun := β u, map_zero' := hβ0' u, map_add' := hβ2 u }
  have hDm : ∀ u w, Dm u w = β u w := fun _ _ => rfl
  have hDmc : ∀ u, Continuous (Dm u) := fun u =>
    hβc.comp (Continuous.prodMk continuous_const continuous_id)
  set P : AddSubgroup X := L.map (Dm x) with hPdef
  have hPset : (P : Set X) = β x '' (L : Set V) := by
    rw [hPdef, AddSubgroup.coe_map]
    rfl
  have hPo : IsOpen (P : Set X) := by rw [hPset]; exact hxo
  have hPc : IsCompact (P : Set X) := by rw [hPset]; exact hLc.image (hDmc x)
  have hπP : ∀ p ∈ P, π • p ∈ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    exact AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, by rw [hDm, hDm, hβs]⟩
  have hπkP : ∀ k : ℕ, ∀ p ∈ P, π ^ k • p ∈ P := by
    intro k
    induction k with
    | zero => intro p hp; simpa using hp
    | succ k ih =>
      intro p hp
      rw [pow_succ, mul_smul]
      exact ih _ (hπP p hp)
  set πP := smulSub π P with hπPdef
  have hπPo : IsOpen (πP : Set X) := isOpen_smulSub π hπ0 P hPo
  have hN1 : ∀ᶠ u in 𝓝 (0 : V), ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X) := by
    have hP : ∀ w ∈ (L : Set V), ∀ᶠ q : V × V in 𝓝 ((0 : V), w), β q.1 q.2 ∈ (πP : Set X) := by
      intro w _
      have h := hβc.tendsto ((0 : V), w)
      have hm : β ((0 : V), w).1 ((0 : V), w).2 ∈ (πP : Set X) := by
        show β 0 w ∈ (πP : Set X)
        rw [hβ0]
        exact πP.zero_mem
      exact h (hπPo.mem_nhds hm)
    exact hLc.eventually_forall_of_forall_eventually
      (P := fun (u : V) (w : V) => β u w ∈ (πP : Set X)) hP
  obtain ⟨N2, hN2, hsm⟩ := hsmall πP (hπPo.mem_nhds πP.zero_mem)
  refine ⟨{u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2, inter_mem hN1 hN2, ?_⟩
  rintro y hy Λ0 ⟨c, hc0, rfl⟩ hsub
  have hcL : ∀ w ∈ L, c • w ∈ {u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2 :=
    fun w hw => hsub (AddSubgroup.mem_map.2 ⟨w, hw, rfl⟩)
  have hcG : ∀ w ∈ L, c • G w ∈ πP := hsm c (fun w hw => (hcL w hw).2)
  have hreach : ∀ p ∈ P, ∃ l ∈ L, Dm y l = p := by
    refine reach_of_approx π hπ L hLc hπL (Dm y) (hDmc y) (fun t w => hβs t y w) P hPc ?_
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    refine ⟨l, hl, ?_⟩
    have e : Dm x l - Dm y l = -(β (y - x) l) := by
      rw [hDm, hDm]
      have := hβ1 x (y - x) l
      rw [add_sub_cancel] at this
      rw [this]
      abel
    rw [e]
    exact πP.neg_mem (hy.1 l hl)
  set Q := L.map (Dm y) with hQdef
  have hPQ : P ≤ Q := fun p hp => by
    obtain ⟨l, hl, e⟩ := hreach p hp
    exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  have hQo : IsOpen (Q : Set X) := AddSubgroup.isOpen_mono hPQ hPo
  have hQc : IsCompact (Q : Set X) := by rw [hQdef, AddSubgroup.coe_map]; exact hLc.image (hDmc y)
  set s : ℕ → K := fun n => π ^ n * c with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero n hπ0) hc0
  have hsc : s 0 = c := by simp [hsdef]
  set Λ : ℕ → AddSubgroup V := fun n => smulSub (s n) L with hΛdef
  have hH : ∀ n, (Λ n).map (Dm y) = smulSub (s n) Q := by
    intro n
    ext z
    rw [AddSubgroup.mem_map, mem_smulSub]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hv
      exact ⟨Dm y l, AddSubgroup.mem_map_of_mem _ hl, by rw [hDm, hDm, hβs]⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
      exact ⟨s n • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, by rw [hDm, hDm, hβs]⟩
  refine ⟨Λ, fun n => (Λ n).map (Dm y), Dm y, ?_, fun n => isOpen_smulSub _ (hs0 n) L hLo,
    fun n => isCompact_smulSub _ L hLc, ?_, ?_, ?_, ?_, fun n => rfl, ?_⟩
  · simp only [hΛdef, smulSub, hsc]
  · refine antitone_nat_of_succ_le fun n z hz => ?_
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hz
    refine (mem_smulSub _ _ _).2 ⟨π • l, hπL l hl, ?_⟩
    rw [smul_smul]
    congr 1
    simp only [hsdef]
    ring
  · intro n
    show IsOpen (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isOpen_smulSub _ (hs0 n) Q hQo
  · intro n
    show IsCompact (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isCompact_smulSub _ Q hQc
  · intro N' hN'
    have hst : Tendsto s atTop (𝓝 0) := by
      have := hπ.mul_const c
      simpa [hsdef] using this
    obtain ⟨k, hk⟩ := eventually_smul_sub (Q : Set X) hQc s hst N' hN'
    refine ⟨k, ?_⟩
    show (((Λ k).map (Dm y) : AddSubgroup X) : Set X) ⊆ N'
    rw [hH, coe_smulSub]
    rintro _ ⟨q, hq, rfl⟩
    exact hk q hq
  · intro n Z hZ W hW
    obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hsc]
    show G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) ∈ (Λ (n + 1)).map (Dm y)
    have e1 : G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) =
        β (c • z) (s n • w) + G (s n • w) := by
      rw [hG (y + c • z) (s n • w), hβ1 y (c • z)]
      abel
    obtain ⟨p1, hp1, e2⟩ := (mem_smulSub _ _ _).1 ((hcL z hz).1 w hw)
    obtain ⟨p2, hp2, e3⟩ := (mem_smulSub _ _ _).1 (hcG w hw)
    have e4 : β (c • z) (s n • w) + G (s n • w) = s (n + 1) • (p1 + π ^ n • p2) := by
      rw [hβs, hGs, ← e2]
      have e5 : s n • s n • G w = s n • π ^ n • (c • G w) := by
        simp only [hsdef]
        module
      rw [e5, ← e3]
      simp only [hsdef]
      module
    rw [e1, e4, hH]
    exact (mem_smulSub _ _ _).2 ⟨_, hPQ (P.add_mem hp1 (hπkP n p2 hp2)), rfl⟩

end Abs

end PI.VolStabW
