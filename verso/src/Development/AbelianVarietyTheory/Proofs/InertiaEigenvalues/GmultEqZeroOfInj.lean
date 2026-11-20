import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.PhiGam.Compare
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Establish `hSQ : Q ≤ Q.comap S` using `fun p hp => hQ p hp`. Set `Sq` to `Q.mapQ Q S hSQ`. Establish `hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `⟨S p, hP p hp, rfl⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `hinj`. Establish `hi : Function.Injective (Sq.restrict hSq)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨_, p, hp, rfl⟩ hz`.

Establish `h1 : Q.mkQ (S p) = 0` using `congrArg Subtype.val hz`. Establish `h2 : p ∈ Q` using `hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)`. Conclude with `Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)`. Establish `hs` using `LinearMap.injective_iff_surjective.mp hi`. Introduce `y hy`.

Take `⟨⟨_, p, hp, rfl⟩, hz⟩` from `hs ⟨Q.mkQ y, y, hy, rfl⟩`. Establish `h1 : Q.mkQ (S p) = Q.mkQ y` using `congrArg Subtype.val hz`. Conclude with `⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩`. Introduce `hsur`. Establish `hs : Function.Surjective (Sq.restrict hSq)`.

Introduce and unpack `⟨_, y, hy, rfl⟩`. Take `⟨p, hp, h⟩` from `hsur y hy`. Use `⟨⟨Q.mkQ p, p, hp, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `((Submodule.Quotient.eq _).mpr h).symm`. Establish `hi` using `LinearMap.injective_iff_surjective.mpr hs`.

Introduce `p hp h`. Establish `h0 : Sq.restrict hSq ⟨Q.mkQ p, p, hp, rfl⟩ = 0` using `Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)`. Establish `h1` using `(injective_iff_map_eq_zero _).mp hi _ h0`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)`.
-/
theorem inj_iff_surj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, S p ∈ P) (hQ : ∀ p ∈ Q, S p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] :
    (∀ p ∈ P, S p ∈ Q → p ∈ Q) ↔ ∀ y ∈ P, ∃ p ∈ P, y - S p ∈ Q := by
  have hSQ : Q ≤ Q.comap S := fun p hp => hQ p hp
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, hP p hp, rfl⟩
  constructor
  · intro hinj
    have hi : Function.Injective (Sq.restrict hSq) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨_, p, hp, rfl⟩ hz
      have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
      have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
    have hs := LinearMap.injective_iff_surjective.mp hi
    intro y hy
    obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
    have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
    exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩
  · intro hsur
    have hs : Function.Surjective (Sq.restrict hSq) := by
      rintro ⟨_, y, hy, rfl⟩
      obtain ⟨p, hp, h⟩ := hsur y hy
      refine ⟨⟨Q.mkQ p, p, hp, rfl⟩, Subtype.ext ?_⟩
      exact ((Submodule.Quotient.eq _).mpr h).symm
    have hi := LinearMap.injective_iff_surjective.mpr hs
    intro p hp h
    have h0 : Sq.restrict hSq ⟨Q.mkQ p, p, hp, rfl⟩ = 0 :=
      Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)
    have h1 := (injective_iff_map_eq_zero _).mp hi _ h0
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)

/- English proof (translation)
Unfold `gmult`. Use `set S := T - algebraMap k (Module.End k U) x with hS`. Establish `h1 : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ Q → p ∈ Q`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro p _ hp`. Simplify using `using hp`. Consider the case `succ m ih`. Introduce `p hp hq`. Rewrite `hq` using `[pow_succ, Module.End.mul_apply]`.

Conclude with `h p hp (ih _ (hP p hp) hq)`. Establish `hmono : Monotone fun m : ℕ => Q.comap (S ^ m)`. Use `monotone_nat_of_le_succ fun m p hp => ?_` and prove the remaining obligations. Rewrite `hp`, the goal using `[Submodule.mem_comap]`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Conclude with `hQ _ hp`. Establish `htop : Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨p, hp, hp'⟩ _`. Take `⟨m, hm⟩` from `(Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hp'`.

Conclude with `h1 m p hp hm`. Rewrite using `[htop]`. Conclude with `Module.finrank_zero_of_subsingleton`.
-/
theorem gmult_eq_zero_of_inj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (x : k)
    (hP : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ P)
    (hQ : ∀ p ∈ Q, (T - algebraMap k (Module.End k U) x) p ∈ Q)
    (h : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ Q → p ∈ Q) : gmult T P Q x = 0 := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) x with hS
  have h1 : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      exact h p hp (ih _ (hP p hp) hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  have htop : Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, hp, hp'⟩ _
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hp'
    exact h1 m p hp hm
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

/- English proof (translation)
Use `haveI := Window.finite_quot hN`. Take `⟨h1, -⟩` from `Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k) (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (y + b) h`. Establish `hv : vv k ≠ 0` using `vv_ne_zero k`. Introduce `x hx hx'`. Take `⟨n, hn, rfl⟩` from `mem_sh_iff_exists.mp hx`.

Take `⟨n', hn', e⟩` from `Window.nab_shift R hg hC b hn`. Take `⟨t, ht, e'⟩` from `mem_sh_iff_exists.mp hx'`. Establish `hc : y • vv k ^ b • n = vv k ^ b • y • n`. Rewrite using `[← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ y), ← const_smul_eq, smul_assoc, one_smul]`. Rewrite `e'` using `[e, hc, ← smul_sub, zpow_add_one₀ hv, mul_smul]`.

Establish `e2` using `smul_right_injective V (zpow_ne_zero b hv) e'`. Establish `: n ∈ sh 1 N` using `h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by`. Rewrite using `[zpow_one, smul_sub, e2, add_smul]`. Use the proof step `abel⟩)`. Take `⟨r, hr, rfl⟩` from `mem_sh_iff_exists.mp this`.

Conclude with `mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩`.
-/
theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (y : k) (h : sen g N (y + b) = 0) :
    ∀ x ∈ sh b N, nab g x - y • x ∈ sh (b + 1) N → x ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (y + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro x hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : y • vv k ^ b • n = vv k ^ b • y • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ y), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, ← smul_sub, zpow_add_one₀ hv, mul_smul] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

/- English proof (translation)
Introduce `k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N₁ N₂ h₁ h₂ c₁ c₂ s lo hi y hy`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hy` to reduce the goal to its premises. Use `set S : Module.End k V := nab g - algebraMap k (Module.End k V) y with hSdef`.

Establish `hS : ∀ p, S p = nab g p - y • p` using `fun p => rfl`. Establish `st : ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ b : ℤ, ∀ p ∈ sh b N, S p ∈ sh b N` using `fun N c b p hp => by`. Rewrite using `[hS]`. Conclude with `(sh b N).sub_mem (Window.nab_mem_sh R hg c b hp) (((sh b N).restrictScalars k).smul_mem y hp)`. Establish `st2 : ∀ p ∈ N₂, S p ∈ N₂`.

Use `st N₂ c₂ 0` as an intermediate fact. Rewrite `this` using `[sh_zero_eq]`. Then use the resulting hypothesis. Establish `key : ∀ m : ℕ, m ≤ 2 * s + 1 → ∀ x ∈ N₂, ∃ p ∈ N₂, x - S p ∈ sh (-s + m) N₁`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro _ x hx; exact ⟨0, N₂.zero_mem, by simpa using hi hx⟩`. Consider the case `succ m ih`. Introduce `hm x hx`. Take `⟨p, hp, hp'⟩` from `ih (by omega) x hx`. Use `set b : ℤ := -s + m with hb`.

Establish `hsen` using `hcon b (by rw [abs_le]; omega)`. Establish `hf` using `Window.finite_quot (h₁.shift b).1`. Rewrite `hf` using `[sh_sh_eq, add_comm]`. Use `haveI : FiniteDimensional k (((N₂ ⊓ sh b N₁).restrictScalars k).map ((sh (b + 1) N₁).restrictScalars k).mkQ) := Submodule.finiteDimensional_of_le (S₂ := ((sh b N₁).restrictScalars k).map ((sh (b + 1) N₁).restrictScalars k).mkQ) (Submodule.map_mono fun z hz => hz.2)`. Take `⟨q, hq, hq'⟩` from `(inj_iff_surj S ((N₂ ⊓ sh b N₁).restrictScalars k) ((sh (b + 1) N₁).restrictScalars k) (fun z hz => ⟨st2 z hz.1, st N₁ c₁ b z hz.2⟩) (fun z hz => st N₁ c₁ _ z hz)).mp (fun z hz hz' => graded_inj R hg h₁.1 c₁ b y hsen z hz.2 hz') (x - S p) ⟨N₂.sub_mem hx (st2 p hp), hp'⟩`.

Use `⟨p + q, N₂.add_mem hp hq.1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← sub_sub, Nat.cast_succ, ← add_assoc]`. Conclude with `hq'`. Use `haveI := Window.finite_quot h₂.1`. Use `gmult_eq_zero_of_inj (nab g) _ _ y st2 (st N₂ c₂ 1) ?_` and prove the remaining obligations.

Use `(inj_iff_surj S (N₂.restrictScalars k) ((sh 1 N₂).restrictScalars k) st2 (st N₂ c₂ 1)).mpr ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨p, hp, hp'⟩` from `key (2 * s + 1) le_rfl x hx`. Use `⟨p, hp, sh_le_sh 1 lo ?_⟩` and prove the remaining obligations. Rewrite using `[sh_sh_eq]`.

Use `hp' using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sen_compare : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N₁ N₂ : Submodule k⟦X⟧ V, IsLat N₁ → IsLat N₂ → CondC g N₁ → CondC g N₂ → ∀ s : ℕ, sh s N₁ ≤ N₂ → N₂ ≤ sh (-s) N₁ → ∀ y : k, sen g N₂ y ≠ 0 → ∃ j : ℤ, |j| ≤ s ∧ sen g N₁ (y + j) ≠ 0 := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N₁ N₂ h₁ h₂ c₁ c₂ s lo hi y hy
  by_contra hcon
  push_neg at hcon
  apply hy
  set S : Module.End k V := nab g - algebraMap k (Module.End k V) y with hSdef
  have hS : ∀ p, S p = nab g p - y • p := fun p => rfl
  have st : ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ b : ℤ, ∀ p ∈ sh b N, S p ∈ sh b N := fun N c b p hp => by
    rw [hS]
    exact (sh b N).sub_mem (Window.nab_mem_sh R hg c b hp) (((sh b N).restrictScalars k).smul_mem y hp)
  have st2 : ∀ p ∈ N₂, S p ∈ N₂ := by
    have := st N₂ c₂ 0
    rwa [sh_zero_eq] at this
  have key : ∀ m : ℕ, m ≤ 2 * s + 1 → ∀ x ∈ N₂, ∃ p ∈ N₂, x - S p ∈ sh (-s + m) N₁ := by
    intro m
    induction m with
    | zero => intro _ x hx; exact ⟨0, N₂.zero_mem, by simpa using hi hx⟩
    | succ m ih =>
      intro hm x hx
      obtain ⟨p, hp, hp'⟩ := ih (by omega) x hx
      set b : ℤ := -s + m with hb
      have hsen := hcon b (by rw [abs_le]; omega)
      have hf := Window.finite_quot (h₁.shift b).1
      rw [sh_sh_eq, add_comm] at hf
      haveI : FiniteDimensional k (((N₂ ⊓ sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) :=
        Submodule.finiteDimensional_of_le (S₂ := ((sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) (Submodule.map_mono fun z hz => hz.2)
      obtain ⟨q, hq, hq'⟩ := (inj_iff_surj S ((N₂ ⊓ sh b N₁).restrictScalars k)
        ((sh (b + 1) N₁).restrictScalars k) (fun z hz => ⟨st2 z hz.1, st N₁ c₁ b z hz.2⟩)
        (fun z hz => st N₁ c₁ _ z hz)).mp
        (fun z hz hz' => graded_inj R hg h₁.1 c₁ b y hsen z hz.2 hz') (x - S p)
        ⟨N₂.sub_mem hx (st2 p hp), hp'⟩
      refine ⟨p + q, N₂.add_mem hp hq.1, ?_⟩
      rw [map_add, ← sub_sub, Nat.cast_succ, ← add_assoc]
      exact hq'
  haveI := Window.finite_quot h₂.1
  refine gmult_eq_zero_of_inj (nab g) _ _ y st2 (st N₂ c₂ 1) ?_
  refine (inj_iff_surj S (N₂.restrictScalars k) ((sh 1 N₂).restrictScalars k) st2 (st N₂ c₂ 1)).mpr ?_
  intro x hx
  obtain ⟨p, hp, hp'⟩ := key (2 * s + 1) le_rfl x hx
  refine ⟨p, hp, sh_le_sh 1 lo ?_⟩
  rw [sh_sh_eq]
  convert hp' using 2
  push_cast; ring

end GlobalTheory.PhiGam.Compare
