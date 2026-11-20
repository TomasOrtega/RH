import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.PhiGam.QuotShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

section lin
variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

/- English proof (translation)
Establish `hmono : Monotone fun m : ℕ => Q.comap (S ^ m)`. Use `monotone_nat_of_le_succ fun m y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, pow_succ', Module.End.mul_apply]`. Conclude with `hQ _ hy`. Rewrite using `[Submodule.mem_iSup_of_directed _ hmono.directed_le]`.

Both sides reduce to the same expression.
-/
theorem mem_iSup_comap_pow (S : Module.End k U) (Q : Submodule k U) (hQ : ∀ q ∈ Q, S q ∈ Q) (p : U) :
    p ∈ ⨆ m : ℕ, Q.comap (S ^ m) ↔ ∃ m : ℕ, (S ^ m) p ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact hQ _ hy
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

/- English proof (translation)
Use `set S := T - algebraMap k (Module.End k U) y with hS`. Use `set S' := T' - algebraMap k (Module.End k U) x with hS'`. Establish `hSa : ∀ p, S p = T p - y • p` using `fun p => by simp [hS, Module.algebraMap_end_apply]`. Establish `hSa' : ∀ p, S' p = T' p - x • p` using `fun p => by simp [hS', Module.algebraMap_end_apply]`. Establish `hSP : ∀ p ∈ P, S p ∈ P` using `fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)`.

Establish `hSQ : ∀ p ∈ Q, S p ∈ Q` using `fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)`. Establish `hSQ' : ∀ p ∈ Q', S' p ∈ Q'` using `fun p hp => by`. Rewrite using `[hSa']`. Conclude with `Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)`. Establish `key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q'`.

Introduce `p hp m`. Proceed by induction on `m with`. Consider the case `zero => simpa using hp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]`.

Use `⟨hSP _ ih.1, ?_⟩` and prove the remaining obligations. Establish `h1` using `hSQ' _ ih.2`. Establish `h2` using `h _ ih.1`. Rewrite `h2` using `[← hSa, ← hSa']`. Establish `h3` using `Q'.add_mem h1 h2`.

Rewrite `h3` using `[map_sub, sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m))`. Introduce `p`. Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']`. Use `and_congr_right fun hp => exists_congr fun m => ?_` and prove the remaining obligations.

Rewrite using `[← hQ']`. Use `(key p hp m).2` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Simplify using `using Q'.sub_mem h1 this`.

Introduce `h1`. Simplify using `using Q'.add_mem this h1`. Unfold `gmult`. Rewrite using `[← hS, ← hS']`. Use `set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)`.

Use `set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)`. Establish `hA : A.map (e : U →ₗ[k] U) = A'`. Use extensionality with `z`. Take `⟨w, rfl⟩` from `e.surjective z`. Rewrite using `[hmem]`.

Conclude with `Submodule.map_equiv_eq_comap_symm e A ▸ by simp`. Set `e' : A ≃ₗ[k] A'` to `e.ofSubmodules A A' hA`. Use `(Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm` and prove the remaining obligations. Use extensionality with `z`. Take `⟨w, rfl⟩` from `e'.surjective z`.

Establish `: (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A` using `hQ' w`. Rewrite using `[this]`. Conclude with `Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp`.
-/
theorem gmult_transport (T T' : Module.End k U) (e : U ≃ₗ[k] U) (P Q P' Q' : Submodule k U)
    (hP' : ∀ p, e p ∈ P' ↔ p ∈ P) (hQ' : ∀ p, e p ∈ Q' ↔ p ∈ Q)
    (hTP : ∀ p ∈ P, T p ∈ P) (hTQ : ∀ p ∈ Q, T p ∈ Q) (hTQ' : ∀ p ∈ Q', T' p ∈ Q') (x y : k)
    (h : ∀ p ∈ P, (T' (e p) - x • e p) - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  set S := T - algebraMap k (Module.End k U) y with hS
  set S' := T' - algebraMap k (Module.End k U) x with hS'
  have hSa : ∀ p, S p = T p - y • p := fun p => by simp [hS, Module.algebraMap_end_apply]
  have hSa' : ∀ p, S' p = T' p - x • p := fun p => by simp [hS', Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hSa]; exact P.sub_mem (hTP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hSa]; exact Q.sub_mem (hTQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hSa']; exact Q'.sub_mem (hTQ' p hp) (Q'.smul_mem _ hp)
  have key : ∀ p ∈ P, ∀ m : ℕ, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro p hp m
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ ih.1, ?_⟩
      have h1 := hSQ' _ ih.2
      have h2 := h _ ih.1
      rw [← hSa, ← hSa'] at h2
      have h3 := Q'.add_mem h1 h2
      rwa [map_sub, sub_add_sub_cancel] at h3
  have hmem : ∀ p, e p ∈ (P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)) ↔ p ∈ (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) := by
    intro p
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_iSup_comap_pow S Q hSQ, mem_iSup_comap_pow S' Q' hSQ', hP']
    refine and_congr_right fun hp => exists_congr fun m => ?_
    rw [← hQ']
    have := (key p hp m).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 this
    · intro h1; simpa using Q'.add_mem this h1
  unfold gmult
  rw [← hS, ← hS']
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m)
  have hA : A.map (e : U →ₗ[k] U) = A' := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem]
    exact Submodule.map_equiv_eq_comap_symm e A ▸ by simp
  let e' : A ≃ₗ[k] A' := e.ofSubmodules A A' hA
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') e' ?_).finrank_eq.symm
  ext z
  obtain ⟨w, rfl⟩ := e'.surjective z
  have : (e' w ∈ Q'.submoduleOf A') ↔ w ∈ Q.submoduleOf A := hQ' w
  rw [this]
  exact Submodule.map_equiv_eq_comap_symm e' _ ▸ by simp

/- English proof (translation)
Establish `: A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h)`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `infer_instance`.
-/
theorem fin_of_le {A B C : Submodule k U} (h : C ≤ B) (hf : FiniteDimensional k (A.map C.mkQ)) :
    FiniteDimensional k (A.map B.mkQ) := by
  have : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [this]; infer_instance

/- English proof (translation)
Establish `e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h)`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression. Rewrite `h1` using `[e]`. Establish `hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ`.

Introduce and unpack `_ ⟨⟨a, -, rfl⟩, ha⟩`. Conclude with `⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩`. Establish `h3` using `Submodule.finiteDimensional_of_le hle`. Conclude with `Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h) (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))`.
-/
theorem fin_trans {A B C : Submodule k U} (h : C ≤ B) (h1 : FiniteDimensional k (A.map B.mkQ))
    (h2 : FiniteDimensional k (B.map C.mkQ)) : FiniteDimensional k (A.map C.mkQ) := by
  have e : A.map B.mkQ = (A.map C.mkQ).map (Submodule.factor h) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h1
  have hle : A.map C.mkQ ⊓ LinearMap.ker (Submodule.factor h) ≤ B.map C.mkQ := by
    rintro _ ⟨⟨a, -, rfl⟩, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero B).1 ha, rfl⟩
  have h3 := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor h)
    (Module.Finite.iff_fg.1 h1) (Module.Finite.iff_fg.1 h3))

/- English proof (translation)
Establish `e` using `LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)`. Rewrite `e` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ]`. Conclude with `e.symm.finiteDimensional`.
-/
theorem fin_quot {A B : Submodule k U} (h : FiniteDimensional k (A.map B.mkQ)) :
    FiniteDimensional k (↥A ⧸ B.submoduleOf A) := by
  have e := LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at e
  exact e.symm.finiteDimensional

/- English proof (translation)
Unfold `gmult`. Rewrite using `[Submodule.submoduleOf_eq_top.2 inf_le_left]`. Conclude with `Module.finrank_zero_of_subsingleton`.
-/
theorem gmult_self (T : Module.End k U) (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  rw [Submodule.submoduleOf_eq_top.2 inf_le_left]
  exact Module.finrank_zero_of_subsingleton

end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
/- English proof (translation)
Establish `: sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P)` using `Submodule.map_sup _ _ _`. Rewrite using `[this, sh_sh_eq]`. Use `sup_le ?_ (by exact_mod_cast h)` and prove the remaining obligations. Simplify `sh_le_sh_of_le (Int.natCast_nonneg m) Q` using `[sh_zero_eq]`.
-/
theorem sh_sup_le {P Q : Submodule k⟦X⟧ V} {m : ℕ} (h : sh ((m + 1 : ℕ) : ℤ) P ≤ Q) :
    sh (m : ℤ) (Q ⊔ sh 1 P) ≤ Q := by
  have : sh (m : ℤ) (Q ⊔ sh 1 P) = sh (m : ℤ) Q ⊔ sh (m : ℤ) (sh 1 P) := Submodule.map_sup _ _ _
  rw [this, sh_sh_eq]
  refine sup_le ?_ (by exact_mod_cast h)
  simpa [sh_zero_eq] using sh_le_sh_of_le (Int.natCast_nonneg m) Q

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
/- English proof (translation)
Simplify `sh_le_sh_of_le (zero_le_one' ℤ) P` using `[sh_zero_eq]`.
-/
theorem sh_one_le (P : Submodule k⟦X⟧ V) : sh 1 P ≤ P := by
  simpa [sh_zero_eq] using sh_le_sh_of_le (zero_le_one' ℤ) P

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `P Q _ _ h`. Establish `: (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥`. Rewrite using `[← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]`.

Rewrite `h` using `[Nat.cast_zero, sh_zero_eq]`. Conclude with `h`. Rewrite using `[this]`. Use `infer_instance`. Consider the case `succ m ih`.

Introduce `P Q hP hQ h`. Use `fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_ (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))` and prove the remaining obligations. Conclude with `fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)`.
-/
theorem fin_lat (m : ℕ) : ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → sh (m : ℤ) P ≤ Q →
    FiniteDimensional k ((P.restrictScalars k).map (Q.restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    intro P Q _ _ h
    have : (P.restrictScalars k).map (Q.restrictScalars k).mkQ = ⊥ := by
      rw [← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      rw [Nat.cast_zero, sh_zero_eq] at h
      exact h
    rw [this]; infer_instance
  | succ m ih =>
    intro P Q hP hQ h
    refine fin_trans (B := (Q ⊔ sh 1 P).restrictScalars k) (fun y hy => Submodule.mem_sup_left hy) ?_
      (ih _ _ (hQ.sup (hP.map _)) hQ (sh_sup_le h))
    exact fin_of_le (fun y hy => Submodule.mem_sup_right hy) (Window.finite_quot hP)

/- English proof (translation)
Establish `hv` using `vv_ne_zero k`. Set `e : V ≃ₗ[k] V` to `(LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k`. Establish `he : ∀ p, e p = vv k • p` using `fun p => rfl`. Establish `hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k`. Introduce `N p`.

Rewrite using `[Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul, zpow_neg_one, inv_mul_cancel₀ hv, one_smul]`. Use `gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp) (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_` and prove the remaining obligations. Take `⟨n', hn', hs⟩` from `Window.nab_shift R hg hP 1 hp`. Rewrite `hs` using `[zpow_one, ← he, ← he]`. Rewrite using `[hs, ← map_smul, ← map_sub, ← map_sub, hN]`.

Establish `: nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n'`. Rewrite using `[Int.cast_one, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)`.
-/
theorem step {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {P Q : Submodule k⟦X⟧ V}
    (hP : CondC g P) (hQ : CondC g Q) (h : sh 1 P ≤ Q) (x : k) :
    qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  have hv := vv_ne_zero k
  let e : V ≃ₗ[k] V := (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k) hv).restrictScalars k
  have he : ∀ p, e p = vv k • p := fun p => rfl
  have hN : ∀ (N : Submodule k⟦X⟧ V) p, e p ∈ (sh 1 N).restrictScalars k ↔ p ∈ N.restrictScalars k := by
    intro N p
    rw [Submodule.restrictScalars_mem, Submodule.restrictScalars_mem, mem_sh_iff_smul_mem, he, smul_smul,
      zpow_neg_one, inv_mul_cancel₀ hv, one_smul]
  refine gmult_transport _ _ e _ _ _ _ (hN P) (hN Q) (fun p hp => Window.nab_mem hP hp)
    (fun p hp => Window.nab_mem hQ hp) (fun p hp => Window.nab_mem_sh R hg hQ 1 hp) _ _ fun p hp => ?_
  obtain ⟨n', hn', hs⟩ := Window.nab_shift R hg hP 1 hp
  rw [zpow_one, ← he, ← he] at hs
  rw [hs, ← map_smul, ← map_sub, ← map_sub, hN]
  have : nab g p - ((1 : ℤ) : k) • p + vv k • n' - x • p - (nab g p - (x + 1) • p) = vv k • n' := by
    rw [Int.cast_one, add_smul]; abel
  rw [this]
  exact h (mem_sh_iff_exists.2 ⟨n', hn', by rw [zpow_one]⟩)

/- English proof (translation)
The claim follows from `GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS (fin_quot (fin_lat m P S hP hS h)) x`.
-/
theorem qmult_add (g : V →ₗ[k] V) (m : ℕ) {P Q S : Submodule k⟦X⟧ V} (hP : P.FG) (hS : S.FG) (h1 : S ≤ Q)
    (h2 : Q ≤ P) (cP : ∀ p ∈ P, nab g p ∈ P) (cQ : ∀ p ∈ Q, nab g p ∈ Q) (cS : ∀ p ∈ S, nab g p ∈ S)
    (h : sh (m : ℤ) P ≤ S) (x : k) : qmult g P S x = qmult g P Q x + qmult g Q S x :=
  GmultAdd.main (nab g) (P.restrictScalars k) (Q.restrictScalars k) (S.restrictScalars k) h1 h2 cP cQ cS
    (fin_quot (fin_lat m P S hP hS h)) x

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `P Q _ _ hle _ _ h`. Rewrite `h` using `[Nat.cast_zero, sh_zero_eq]`. Rewrite using `[le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]`.

Consider the case `succ m ih`. Introduce `P Q hP hQ hle cP cQ h`. Establish `hle' : Q ⊔ sh 1 P ≤ P` using `sup_le hle (sh_one_le P)`. Establish `cQ' : CondC g (Q ⊔ sh 1 P)`. Rewrite using `[condC_iff_nab_mem]`.

Introduce `y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)`. Establish `h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q`.

Rewrite using `[sh_sh_eq, add_comm, ← sh_sh_eq]`. Conclude with `sh_le_sh 1 h`. Establish `a1` using `qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp) (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)`. Establish `a2` using `qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _) (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x`. Rewrite using `[a1, a2, step R hg cP cQ' le_sup_right, ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]`.
-/
theorem shift_of_le {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) (x : k) (m : ℕ) :
    ∀ P Q : Submodule k⟦X⟧ V, P.FG → Q.FG → Q ≤ P → CondC g P → CondC g Q → sh (m : ℤ) P ≤ Q →
      qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  induction m with
  | zero =>
    intro P Q _ _ hle _ _ h
    rw [Nat.cast_zero, sh_zero_eq] at h
    rw [le_antisymm hle h, qmult, qmult, gmult_self, gmult_self]
  | succ m ih =>
    intro P Q hP hQ hle cP cQ h
    have hle' : Q ⊔ sh 1 P ≤ P := sup_le hle (sh_one_le P)
    have cQ' : CondC g (Q ⊔ sh 1 P) := by
      rw [condC_iff_nab_mem]
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact Submodule.add_mem_sup (Window.nab_mem cQ ha) (Window.nab_mem_sh R hg cP 1 hb)
    have h' : sh ((m + 1 : ℕ) : ℤ) (sh 1 P) ≤ sh 1 Q := by
      rw [sh_sh_eq, add_comm, ← sh_sh_eq]; exact sh_le_sh 1 h
    have a1 := qmult_add g (m + 1) hP hQ (le_sup_left (b := sh 1 P)) hle' (fun p hp => Window.nab_mem cP hp)
      (fun p hp => Window.nab_mem cQ' hp) (fun p hp => Window.nab_mem cQ hp) h (x + 1)
    have a2 := qmult_add g (m + 1) (P := sh 1 P) (Q := sh 1 (Q ⊔ sh 1 P)) (S := sh 1 Q) (hP.map _) (hQ.map _)
      (sh_le_sh 1 le_sup_left) (sh_le_sh 1 hle') (fun p hp => Window.nab_mem_sh R hg cP 1 hp)
      (fun p hp => Window.nab_mem_sh R hg cQ' 1 hp) (fun p hp => Window.nab_mem_sh R hg cQ 1 hp) h' x
    rw [a1, a2, step R hg cP cQ' le_sup_right,
      ih (Q ⊔ sh 1 P) Q (hQ.sup (hP.map _)) hQ le_sup_left cQ' cQ (sh_sup_le h)]

/- English proof (translation)
Introduce `k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x`. Take `⟨m, hm⟩` from `Close.exists_pow hP.1 hQ.2`. Conclude with `shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)`.
-/
theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg P Q hP hQ hle cP cQ x
  obtain ⟨m, hm⟩ := Close.exists_pow hP.1 hQ.2
  exact shift_of_le R hg x m P Q hP.1 hQ.1 hle cP cQ (Close.sh_le hm)

end GlobalTheory.PhiGam.QuotShift
