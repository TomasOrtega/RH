import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.SenAdd

section
variable {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ m ih`. Introduce `y hy`.

Rewrite using `[pow_succ, Module.End.mul_apply]`. Apply `ih` to reduce the goal to its premises. Rewrite using `[LinearMap.sub_apply, Module.algebraMap_end_apply]`. Conclude with `Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)`.
-/
theorem pow_mem (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (m : ℕ) :
    ∀ y ∈ Q, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)

/- English proof (translation)
Establish `hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)`. Use `monotone_nat_of_le_succ fun m z hz => ?_` and prove the remaining obligations. Rewrite `hz`, the goal using `[Submodule.mem_comap]`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Simplify using `using pow_mem T Q hQ x 1 _ hz`.

Conclude with `Submodule.mem_iSup_of_directed _ hm.directed_le`.
-/
theorem mem_gen (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (y : A) :
    y ∈ (⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)) ↔
      ∃ m : ℕ, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  have hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m z hz => ?_
    rw [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]
    simpa using pow_mem T Q hQ x 1 _ hz
  exact Submodule.mem_iSup_of_directed _ hm.directed_le

/- English proof (translation)
Proceed by induction on `m generalizing y with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Use `congr 1`.

Simplify using `[Module.algebraMap_end_apply, hT]`.
-/
theorem pow_comm (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B) (hT : ∀ y, h (T y) = T' (h y))
    (x : k) (m : ℕ) (y : A) :
    h (((T - algebraMap k (Module.End k A) x) ^ m) y) = ((T' - algebraMap k (Module.End k B) x) ^ m) (h y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [Module.algebraMap_end_apply, hT]

/- English proof (translation)
Establish `hQ : ∀ y ∈ Q, T y ∈ Q` using `fun y hy => (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))`. Unfold `gmult`. Use `set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG`. Use `set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'`. Establish `hGG : ∀ y ∈ G, h y ∈ G'`.

Introduce and unpack `y ⟨hy, hy2⟩`. Take `⟨m, hm⟩` from `(mem_gen T Q hQ x y).1 hy2`. Use `⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← pow_comm T T' h hT]`. Conclude with `(hker _ (hQP hm)).2 hm`.

Set `φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G')` to `(Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG`. Establish `hk : Q.submoduleOf G = LinearMap.ker φ`. Use extensionality with `⟨y, hy⟩`. Rewrite using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `y ∈ Q ↔ Submodule.Quotient.mk _ = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `(hker y hy.1).symm`. Establish `hs : Function.Surjective φ`. Introduce `w`. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`.

Take `⟨y, hy, hzy⟩` from `hsur z hz.1`. Take `⟨m, hm⟩` from `(mem_gen T' Q' hQ' x z).1 hz.2`. Establish `hyG : y ∈ G`. Use `⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩` and prove the remaining obligations. Rewrite using `[pow_comm T T' h hT]`.

Use `Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_sub_cancel]`. Then use the resulting hypothesis. Use `⟨⟨y, hyG⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[eq_comm, Submodule.Quotient.eq]`.

Conclude with `hzy`. Rewrite using `[hk]`. Conclude with `(φ.quotKerEquivOfSurjective hs).finrank_eq`.
-/
theorem gmult_transport (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B)
    (hT : ∀ y, h (T y) = T' (h y)) (P Q : Submodule k A) (P' Q' : Submodule k B)
    (hP : ∀ y ∈ P, T y ∈ P) (hQP : Q ≤ P) (hQ' : ∀ y ∈ Q', T' y ∈ Q')
    (hmap : ∀ y ∈ P, h y ∈ P') (hker : ∀ y ∈ P, h y ∈ Q' ↔ y ∈ Q)
    (hsur : ∀ z ∈ P', ∃ y ∈ P, z - h y ∈ Q') (x : k) : gmult T P Q x = gmult T' P' Q' x := by
  have hQ : ∀ y ∈ Q, T y ∈ Q := fun y hy =>
    (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))
  unfold gmult
  set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG
  set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'
  have hGG : ∀ y ∈ G, h y ∈ G' := by
    rintro y ⟨hy, hy2⟩
    obtain ⟨m, hm⟩ := (mem_gen T Q hQ x y).1 hy2
    refine ⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩
    rw [← pow_comm T T' h hT]
    exact (hker _ (hQP hm)).2 hm
  let φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G') := (Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG
  have hk : Q.submoduleOf G = LinearMap.ker φ := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    change y ∈ Q ↔ Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker y hy.1).symm
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, hy, hzy⟩ := hsur z hz.1
    obtain ⟨m, hm⟩ := (mem_gen T' Q' hQ' x z).1 hz.2
    have hyG : y ∈ G := by
      refine ⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩
      rw [pow_comm T T' h hT]
      have := Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)
      rwa [map_sub, sub_sub_cancel] at this
    refine ⟨⟨y, hyG⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [eq_comm, Submodule.Quotient.eq]
    exact hzy
  rw [hk]
  exact (φ.quotKerEquivOfSurjective hs).finrank_eq

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in

/- English proof (translation)
Use `sh_le_sh_of_le (zero_le_one' ℤ) N` as an intermediate fact. Rewrite `this` using `[sh_zero_eq]`. Then use the resulting hypothesis.
-/
theorem sh_one_le (N : Submodule k⟦X⟧ V) : sh 1 N ≤ N := by
  have := sh_le_sh_of_le (zero_le_one' ℤ) N
  rwa [sh_zero_eq] at this

/- English proof (translation)
Introduce `y hy`. Take `⟨z, hz, rfl⟩` from `mem_sh_iff_exists.1 hy`. Take `⟨κ, -, hκ⟩` from `R.γ_v`. Establish `hv` using `vv_ne_zero k`. Establish `h1` using `hN z hz`.

Establish `h2 : g z ∈ N` using `by simpa using N.add_mem (sh_one_le N h1) hz`. Establish `h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N` using `mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩`. Establish `h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z)`. Rewrite using `[nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv, sub_smul, one_smul, smul_smul, mul_comm (vv k)]`. Express the relevant statement in the definitionally equal form `g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z`.

Normalize the expressions using the abelian group laws. Rewrite using `[h4]`. Conclude with `Submodule.sub_mem _ h1 h3`.
-/
theorem nab_mem_sh_one {l : ℕ} (R : RingPG k l) (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V)
    (hN : CondC g N) : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  have hv := vv_ne_zero k
  have h1 := hN z hz
  have h2 : g z ∈ N := by simpa using N.add_mem (sh_one_le N h1) hz
  have h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩
  have h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z) := by
    rw [nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv,
      sub_smul, one_smul, smul_smul, mul_comm (vv k)]
    change g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z
    abel
  rw [h4]
  exact Submodule.sub_mem _ h1 h3

omit [IsScalarTower k k⸨X⸩ V] in

/- English proof (translation)
Take `⟨s, hs⟩` from `hN`. Establish `hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k` using `Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy`. Establish `key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N`. Introduce `y hy`. Rewrite `hy` using `[← hs]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add y y' _ _ hy hy'`. Take `⟨z, hz, h⟩` from `hy`.

Take `⟨z', hz', h'⟩` from `hy'`. Use `⟨z + z', Submodule.add_mem _ hz hz', ?_⟩` and prove the remaining obligations. Use `Submodule.add_mem _ h h'` as an intermediate fact. Rewrite `this` using `[sub_add_sub_comm]`. Then use the resulting hypothesis. Consider the case `smul a y _ hy`.

Take `⟨z, hz, h⟩` from `hy`. Use `⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩` and prove the remaining obligations. Use `set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a`. Establish `ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a)` using `PowerSeries.eq_X_mul_shift_add_const a`. Establish `h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N` using `mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩`.

Establish `h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z`. Rewrite using `[zpow_one, mul_smul, vv_eq_coe_X]`. Conclude with `algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)`. Establish `h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z`. Rewrite using `[← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h5]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)`. Use `haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s`. Use `Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_` and prove the remaining obligations.

Take `⟨⟨y, hy⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨z, hz, h⟩` from `key y hy`. Use `⟨⟨z, hz⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[eq_comm, Submodule.Quotient.eq]`.

Conclude with `h`.
-/
theorem finite_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    FiniteDimensional k (↥(N.restrictScalars k) ⧸
      ((sh 1 N).restrictScalars k).submoduleOf (N.restrictScalars k)) := by
  obtain ⟨s, hs⟩ := hN
  have hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k :=
    Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy
  have key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, hz, h⟩ := hy
      obtain ⟨z', hz', h'⟩ := hy'
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      have := Submodule.add_mem _ h h'
      rwa [sub_add_sub_comm] at this
    | smul a y _ hy =>
      obtain ⟨z, hz, h⟩ := hy
      refine ⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩
      set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
      have ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a) :=
        PowerSeries.eq_X_mul_shift_add_const a
      have h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩
      have h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [zpow_one, mul_smul, vv_eq_coe_X]
        exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)
      have h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]
        abel
      rw [h5]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)
  haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s
  refine Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z, hz, h⟩ := key y hy
  refine ⟨⟨z, hz⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [eq_comm, Submodule.Quotient.eq]
  exact h

end

/- English proof (translation)
Introduce `k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x`. Establish `hN1` using `(condC_iff_nab_mem gV N).1 hC`. Establish `hN2` using `nab_mem_sh_one R gV hg N hC`. Establish `nf : ∀ y, f (nab gW y) = nab gV (f y)` using `fun y => by`. Rewrite using `[nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]`.

Establish `np : ∀ y, p (nab gV y) = nab gU (p y)` using `fun y => by`. Rewrite using `[nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]`. Use `set N' := N.map (p.restrictScalars k⟦X⟧) with hN'`. Establish `hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u`. Introduce `u`.

Prove the components needed by the constructor for the conclusion. Introduce `hu`. Take `⟨_, ⟨z, hz, rfl⟩, rfl⟩` from `mem_sh_iff_exists.1 hu`. Conclude with `⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨z, hz, rfl⟩` from `mem_sh_iff_exists.1 hy`. Conclude with `mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩`. Establish `hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N'`. Introduce `u hu`. Take `⟨y, hy, rfl⟩` from `(hsh u).1 hu`.

Conclude with `(hsh _).2 ⟨_, hN2 y hy, np y⟩`. Set `Q : Submodule k V` to `N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)`. Establish `hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N'` using `fun _ => Iff.rfl`. Establish `hadd` using `GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k) (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1 (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x`. Establish `e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x` using `gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k) ((sh 1 N').restrictScalars k) hN1 inf_le_left hU (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩) (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x`.

Establish `e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x`. Use `gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x` and prove the remaining obligations. Introduce `y hy`. Express the relevant statement in the definitionally equal form `f (nab gW y) ∈ N`. Rewrite using `[nf]`.

Conclude with `hN1 _ hy`. Introduce `y hy`. Use `(hQ _).2 ⟨hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p (f y) ∈ _`. Rewrite using `[hex.apply_apply_eq_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `y _`. Express the relevant statement in the definitionally equal form `f y ∈ sh 1 N ↔ y ∈ sh 1 _`. Rewrite using `[mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]`. Both sides reduce to the same expression.

Introduce `z hz`. Take `⟨y, hy, hyz⟩` from `(hsh _).1 hz.2`. Take `⟨w, hw⟩` from `(hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)`. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f w ∈ N`.

Rewrite using `[hw]`. Conclude with `N.sub_mem hz.1 (sh_one_le N hy)`. Express the relevant statement in the definitionally equal form `z - f w ∈ sh 1 N`. Rewrite using `[hw, sub_sub_cancel]` and apply the resulting hypothesis. Rewrite using `[e2, ← e1, add_comm]`.

Conclude with `hadd`.
-/
theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] {U : Type} [AddCommGroup U] [Module k⸨X⸩ U] [Module k⟦X⟧ U] [Module k U] [IsScalarTower k⟦X⟧ k⸨X⸩ U] [IsScalarTower k k⸨X⸩ U] [IsScalarTower k k⟦X⟧ U] [FiniteDimensional k⸨X⸩ U] (gV : V →ₗ[k] V) (gW : W →ₗ[k] W) (gU : U →ₗ[k] U) (f : W →ₗ[k⸨X⸩] V) (p : V →ₗ[k⸨X⸩] U), Semi R.γ gV → Function.Injective f → Function.Surjective p → Function.Exact f p → (∀ x, f (gW x) = gV (f x)) → (∀ x, p (gV x) = gU (p x)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC gV N → ∀ x : k, sen gV N x = sen gW (N.comap (f.restrictScalars k⟦X⟧)) x + sen gU (N.map (p.restrictScalars k⟦X⟧)) x := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x
  have hN1 := (condC_iff_nab_mem gV N).1 hC
  have hN2 := nab_mem_sh_one R gV hg N hC
  have nf : ∀ y, f (nab gW y) = nab gV (f y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]
  have np : ∀ y, p (nab gV y) = nab gU (p y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]
  set N' := N.map (p.restrictScalars k⟦X⟧) with hN'
  have hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hu
      exact ⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
      exact mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩
  have hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N' := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hsh u).1 hu
    exact (hsh _).2 ⟨_, hN2 y hy, np y⟩
  let Q : Submodule k V := N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)
  have hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N' := fun _ => Iff.rfl
  have hadd := GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k)
    (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1
    (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x
  have e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x :=
    gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k)
      ((sh 1 N').restrictScalars k) hN1 inf_le_left hU
      (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩)
      (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x
  have e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x := by
    refine gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x
    · intro y hy
      change f (nab gW y) ∈ N
      rw [nf]
      exact hN1 _ hy
    · intro y hy
      refine (hQ _).2 ⟨hy, ?_⟩
      change p (f y) ∈ _
      rw [hex.apply_apply_eq_zero]
      exact Submodule.zero_mem _
    · intro y _
      change f y ∈ sh 1 N ↔ y ∈ sh 1 _
      rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]
      rfl
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (hsh _).1 hz.2
      obtain ⟨w, hw⟩ := (hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)
      refine ⟨w, ?_, ?_⟩
      · change f w ∈ N
        rw [hw]
        exact N.sub_mem hz.1 (sh_one_le N hy)
      · change z - f w ∈ sh 1 N
        rwa [hw, sub_sub_cancel]
  rw [e2, ← e1, add_comm]
  exact hadd

end GlobalTheory.PhiGam.SenAdd
