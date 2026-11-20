import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantKillsCyclicOfZero

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def prodRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V × V') := fun a b => (E a b).prodMap (E' a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem prodRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (z : V × V') :
    prodRepresentation E E' a b z = (E a b z.1, E' a b z.2) := rfl

/- English proof (translation)
Take `⟨x, y⟩` from `z`. Simplify using `[weightSp, forall_and]`.
-/
theorem prod_mem_weightSpace_iff (E : GLOps n K V) (E' : GLOps n K V') (mu : Fin n → ℤ) (z : V × V') :
    z ∈ weightSp (prodRepresentation E E') mu ↔ z.1 ∈ weightSp E mu ∧ z.2 ∈ weightSp E' mu := by
  obtain ⟨x, y⟩ := z
  simp [weightSp, forall_and]

/- English proof (translation)
Take `⟨hE1, -, hE3⟩` from `hE`. Take `⟨hE1', -, hE3'⟩` from `hE'`. Use `⟨fun a b c d => ?_, fun z => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun z => Prod.ext ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `have h := LinearMap.congr_fun (hE1 a b c d) z.1 split_ifs at h ⊢ <;> simpa using h`.

Apply the tactic sequence `have h := LinearMap.congr_fun (hE1' a b c d) z.2 split_ifs at h ⊢ <;> simpa using h`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, y⟩ -`. Establish `hx : x ∈ ⨆ mu, weightSp E mu` using `by rw [hE3]; exact Submodule.mem_top`. Establish `hy : y ∈ ⨆ mu, weightSp E' mu` using `by rw [hE3']; exact Submodule.mem_top`.

Establish `h1 : (⨆ mu, weightSp E mu).map (LinearMap.inl K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_mono fun mu => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite using `[prod_mem_weightSpace_iff]`.

Conclude with `⟨by simpa using hv, by simp⟩`. Establish `h2 : (⨆ mu, weightSp E' mu).map (LinearMap.inr K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_mono fun mu => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Rewrite using `[prod_mem_weightSpace_iff]`. Conclude with `⟨by simp, by simpa using hv⟩`. Establish `hxy : ((x, y) : V × V') = LinearMap.inl K V V' x + LinearMap.inr K V V' y` using `by simp`. Rewrite using `[hxy]`. Conclude with `Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)`.
-/
theorem prodRepresentation_isRep [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V')
    (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (prodRepresentation E E') := by
  obtain ⟨hE1, -, hE3⟩ := hE
  obtain ⟨hE1', -, hE3'⟩ := hE'
  refine ⟨fun a b c d => ?_, fun z => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun z => Prod.ext ?_ ?_
    · have h := LinearMap.congr_fun (hE1 a b c d) z.1
      split_ifs at h ⊢ <;> simpa using h
    · have h := LinearMap.congr_fun (hE1' a b c d) z.2
      split_ifs at h ⊢ <;> simpa using h
  · rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    have hx : x ∈ ⨆ mu, weightSp E mu := by rw [hE3]; exact Submodule.mem_top
    have hy : y ∈ ⨆ mu, weightSp E' mu := by rw [hE3']; exact Submodule.mem_top
    have h1 : (⨆ mu, weightSp E mu).map (LinearMap.inl K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun mu => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [prod_mem_weightSpace_iff]
      exact ⟨by simpa using hv, by simp⟩
    have h2 : (⨆ mu, weightSp E' mu).map (LinearMap.inr K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun mu => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [prod_mem_weightSpace_iff]
      exact ⟨by simp, by simpa using hv⟩
    have hxy : ((x, y) : V × V') = LinearMap.inl K V V' x + LinearMap.inr K V V' y := by simp
    rw [hxy]
    exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)

/- English proof (translation)
Establish `hu' : u' ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E' ab.1 ab.2)` using `hu`. Use `clear hu`. Proceed by induction on `hu' using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`.

Conclude with `⟨E a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩`. Consider the case `one => exact ⟨1, one_mem _, fun y => rfl⟩`. Consider the case `mul x y _ _ ihx ihy`. Take `⟨u1, hu1, h1⟩` from `ihx`. Take `⟨u2, hu2, h2⟩` from `ihy`.

Conclude with `⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (u2 z)).trans (congrArg x (h2 z))⟩`.
-/
theorem equivariant_lifts_monoid (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    {u' : Module.End K V'} (hu : u' ∈ Umon E') : ∃ u ∈ Umon E, ∀ y, T (u y) = u' (T y) := by
  have hu' : u' ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E' ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨E a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩
  | one => exact ⟨1, one_mem _, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, hu1, h1⟩ := ihx
    obtain ⟨u2, hu2, h2⟩ := ihy
    exact ⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (u2 z)).trans (congrArg x (h2 z))⟩

/- English proof (translation)
Establish `hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2)` using `hu`. Use `clear hu`. Proceed by induction on `hu' using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`.

Conclude with `⟨E' a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩`. Consider the case `one => exact ⟨1, one_mem _, fun y => rfl⟩`. Consider the case `mul x y _ _ ihx ihy`. Take `⟨u1, hu1, h1⟩` from `ihx`. Take `⟨u2, hu2, h2⟩` from `ihy`.

Conclude with `⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (y z)).trans (congrArg u1 (h2 z))⟩`.
-/
private theorem exists_Umon_intertwined_of_isEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V')
    (hT : IsEquivariantMap E E' T) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ u' ∈ Umon E', ∀ y, T (u y) = u' (T y) := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨E' a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩
  | one => exact ⟨1, one_mem _, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, hu1, h1⟩ := ihx
    obtain ⟨u2, hu2, h2⟩ := ihy
    exact ⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (y z)).trans (congrArg u1 (h2 z))⟩

/- English proof (translation)
Unfold `cyclicSubmodule`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, ⟨u, hu, rfl⟩, rfl⟩`. Take `⟨u', hu', h⟩` from `exists_Umon_intertwined_of_isEquivariantMap E E' T hT hu`. Conclude with `⟨u', hu', h v⟩`. Introduce and unpack `⟨u', hu', rfl⟩`. Take `⟨u, hu, h⟩` from `equivariant_lifts_monoid E E' T hT hu'`.

Conclude with `⟨u v, ⟨u, hu, rfl⟩, h v⟩`.
-/
theorem equivariant_map_cyclicSubmodule (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V) :
    (cyclicSubmodule E v).map T = cyclicSubmodule E' (T v) := by
  unfold cyclicSubmodule
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨u', hu', h⟩ := exists_Umon_intertwined_of_isEquivariantMap E E' T hT hu
    exact ⟨u', hu', h v⟩
  · rintro ⟨u', hu', rfl⟩
    obtain ⟨u, hu, h⟩ := equivariant_lifts_monoid E E' T hT hu'
    exact ⟨u v, ⟨u, hu, rfl⟩, h v⟩

end

/- English proof (translation)
Establish `hEG0` using `hEG`. Take `⟨hcomm, -, -⟩` from `hEG0`. Take `⟨-, hg0w, hg0r⟩` from `hg0`. Establish `wt : ∀ (μ : Fin n → ℤ) (x : G), x ∈ weightSp EG μ ↔ ∀ a, EG a a x = ((μ a : ℤ) : K) • x`. Introduce `μ x`.

Simplify using `[weightSp, sub_eq_zero]`. Establish `hlam` using `(wt lam g0).mp hg0w`. Establish `comm : ∀ a b c d (y : G), EG c d (EG a b y) = EG a b (EG c d y) + ((if d = a then EG c b y else 0) - (if b = c then EG a d y else 0))`. Introduce `a b c d y`. Establish `h' : EG c d (EG a b y) - EG a b (EG c d y) = (if d = a then EG c b y else 0) - (if b = c then EG a d y else 0)`.

Establish `h` using `LinearMap.congr_fun (hcomm c d a b) y`. Apply the tactic sequence `split_ifs at h ⊢ <;> simpa using h`. Conclude with `sub_eq_iff_eq_add'.mp h'`. Take `⟨L, hL⟩ : ∃ L : Submonoid (Module.End K G), L = Submonoid.closure {x | ∃ a b : Fin n, b < a ∧ x = EG a b}` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N : Submodule K G, N = Submodule.span K {x | ∃ l ∈ L, x = l g0}` from `⟨_, rfl⟩`.

Establish `lowL : ∀ a b : Fin n, b < a → EG a b ∈ L` using `fun a b h => by`. Rewrite using `[hL]`. Conclude with `Submonoid.subset_closure ⟨a, b, h, rfl⟩`. Establish `gen_mem : ∀ l ∈ L, l g0 ∈ N` using `fun l hl => by`. Rewrite using `[hN]`.

Conclude with `Submodule.subset_span ⟨l, hl, rfl⟩`. Establish `g0N : g0 ∈ N` using `by simpa using gen_mem 1 L.one_mem`. Establish `low_mem : ∀ a b : Fin n, b < a → N ≤ N.comap (EG a b)`. Introduce `a b hab`. Use `(le_of_eq hN).trans (Submodule.span_le.mpr ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨l, hl, rfl⟩`. Conclude with `gen_mem _ (L.mul_mem (lowL a b hab) hl)`. Establish `all_gen : ∀ l ∈ L, ∀ c d, EG c d (l g0) ∈ N`. Introduce `l hl`. Rewrite `hl` using `[hL]`.

Proceed by induction on `hl using Submonoid.closure_induction_left with`. Consider the case `one`. Introduce `c d`. Use `show EG c d g0 ∈ N`. Break down `lt_trichotomy c d with h | h | h` into its components or cases.

Rewrite using `[hg0r c d h]`. Conclude with `N.zero_mem`. Rewrite using `[h, hlam d]`. Conclude with `N.smul_mem _ g0N`. Conclude with `gen_mem _ (lowL c d h)`.

Consider the case `mul_left s hs l _ ih`. Take `⟨a, b, hab, rfl⟩` from `hs`. Introduce `c d`. Use `show EG c d (EG a b (l g0)) ∈ N`. Rewrite using `[comm a b c d (l g0)]`.

Apply the tactic sequence `refine N.add_mem (low_mem a b hab (ih c d)) (N.sub_mem ?_ ?_) <;> split_ifs <;> first | exact ih _ _ | exact N.zero_mem`. Establish `all_mem : ∀ c d, ∀ x ∈ N, EG c d x ∈ N`. Introduce `c d`. Establish `hle : N ≤ N.comap (EG c d)`. Use `(le_of_eq hN).trans (Submodule.span_le.mpr ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨l, hl, rfl⟩`. Conclude with `all_gen l hl c d`. Conclude with `fun x hx => hle hx`. Establish `umonS : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → ∀ u ∈ Umon EG, ∀ x ∈ S, u x ∈ S`. Introduce `S hS u hu`.

Establish `hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => EG ab.1 ab.2)` using `hu`. Use `clear hu`. Proceed by induction on `hu' using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`.

Conclude with `fun y hy => hS a b y hy`. Consider the case `one => exact fun y hy => hy`. Consider the case `mul x y _ _ ihx ihy => exact fun z hz => ihx _ (ihy z hz)`. Establish `cycle : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → g0 ∈ S → S = ⊤`. Introduce `S hS hg`.

Rewrite using `[eq_top_iff, ← hcyc]`. Unfold `cyclicSubmodule`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `umonS S hS u hu g0 hg`.

Establish `Ntop : N = ⊤` using `cycle N all_mem g0N`. Take `⟨H, hH⟩ : ∃ H : Module.End K G, H = ∑ c : Fin n, ((c : ℕ) : K) • EG c c` from `⟨_, rfl⟩`. Establish `hHapp : ∀ y, H y = ∑ c : Fin n, ((c : ℕ) : K) • EG c c y`. Introduce `y`. Rewrite using `[hH]`.

Simplify using the standard rewrite rules. Take `⟨h0, hh0⟩ : ∃ h0 : K, h0 = ∑ c : Fin n, ((c : ℕ) : K) * ((lam c : ℤ) : K)` from `⟨_, rfl⟩`. Establish `Hg0 : H g0 = h0 • g0`. Rewrite using `[hHapp, hh0, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[hlam c, smul_smul]`. Establish `Hstep : ∀ (a b : Fin n) (y : G) (t : K), H y = t • y → H (EG a b y) = (t + (((a : ℕ) : K) - ((b : ℕ) : K))) • EG a b y`. Introduce `a b y t hy`. Establish `e1 : ∑ c : Fin n, ((c : ℕ) : K) • EG a b (EG c c y) = EG a b (H y)`. Rewrite using `[hHapp, map_sum]`.

Simplify using `only [map_smul]`. Establish `e2 : ∑ c : Fin n, ((c : ℕ) : K) • (if c = a then EG c b y else 0) = ((a : ℕ) : K) • EG a b y`. Simplify using `[smul_ite]`. Establish `e3 : ∑ c : Fin n, ((c : ℕ) : K) • (if b = c then EG a c y else 0) = ((b : ℕ) : K) • EG a b y`. Simplify using `[smul_ite]`.

Rewrite using `[hHapp]`. Simplify using `only [comm a b, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3, hy, map_smul]`. Rewrite using `[add_smul, sub_smul]`. Establish `alt : ∀ l ∈ L, (∃ r : K, l g0 = r • g0) ∨ ∃ k : ℕ, 0 < k ∧ H (l g0) = (h0 + (k : K)) • l g0`. Introduce `l hl`.

Rewrite `hl` using `[hL]`. Proceed by induction on `hl using Submonoid.closure_induction_left with`. Consider the case `one => exact Or.inl ⟨1, by simp⟩`. Consider the case `mul_left s hs l _ ih`. Take `⟨a, b, hab, rfl⟩` from `hs`.

Establish `hab' : (b : ℕ) < (a : ℕ)` using `hab`. Establish `hcast : ((a : ℕ) : K) - ((b : ℕ) : K) = (((a : ℕ) - (b : ℕ) : ℕ) : K)`. Rewrite using `[Nat.cast_sub hab'.le]`. Use `right`. Break down `ih with ⟨r, hr⟩ | ⟨k, hk0, hHk⟩` into its components or cases.

Use `⟨(a : ℕ) - (b : ℕ), by omega, ?_⟩ show H (EG a b (l g0)) = _ • EG a b (l g0)` and prove the remaining obligations. Rewrite using `[hr, map_smul, map_smul, Hstep a b g0 h0 Hg0, hcast]`. Conclude with `smul_comm _ _ _`. Use `⟨k + ((a : ℕ) - (b : ℕ)), by omega, ?_⟩ show H (EG a b (l g0)) = _ • EG a b (l g0)` and prove the remaining obligations. Rewrite using `[Hstep a b _ _ hHk, hcast, Nat.cast_add, add_assoc]`.

Establish `key : ∀ w : G, H w = h0 • w → ∃ r : K, w = r • g0`. Introduce `w hw`. Establish `hle : N ≤ Submodule.span K {g0} ⊔ ⨆ (μ : K) (_ : μ ≠ h0), Module.End.eigenspace H μ`. Use `(le_of_eq hN).trans (Submodule.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, rfl⟩`.

Break down `alt l hl with ⟨r, hr⟩ | ⟨k, hk, hHk⟩` into its components or cases. Rewrite using `[hr]`. Conclude with `Submodule.mem_sup_left (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self g0))`. Use `Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (h0 + (k : K)) (Submodule.mem_iSup_of_mem ?_ ?_))` and prove the remaining obligations. Introduce `h`.

Establish `: k = 0` using `by simpa using h`. Use linear arithmetic over natural numbers and integers. Conclude with `Module.End.mem_eigenspace_iff.mpr hHk`. Establish `hwN : w ∈ N` using `by rw [Ntop]; exact Submodule.mem_top`. Take `⟨x, hx, z, hz, rfl⟩` from `Submodule.mem_sup.mp (hle hwN)`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hx`. Establish `hz0 : z ∈ Module.End.eigenspace H h0`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Rewrite `hw` using `[map_add, map_smul, Hg0, smul_add, smul_comm h0 r g0]`. Conclude with `add_left_cancel hw`.

Establish `hz' : z = 0` using `(Submodule.mem_bot K).mp ((Module.End.eigenspaces_iSupIndep H h0).le_bot (Submodule.mem_inf.mpr ⟨hz0, hz⟩))`. Conclude with `⟨r, by rw [hz', add_zero]⟩`. Establish `hWs : ∀ a b, ∀ x ∈ LinearMap.ker F, EG a b x ∈ LinearMap.ker F`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hF a b x, hx, map_zero]`. Take `⟨W', hC, hW's⟩` from `h2 K G n EG hEG (LinearMap.ker F) hWs`. Establish `Hmem : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → ∀ x ∈ S, H x ∈ S`. Introduce `S hS x hx`. Rewrite using `[hHapp]`.

Conclude with `S.sum_mem fun c _ => S.smul_mem _ (hS c c x hx)`. Establish `hg : g0 ∈ LinearMap.ker F ⊔ W'` using `by rw [hC.sup_eq_top]; exact Submodule.mem_top`. Take `⟨w, hw, w', hw', hsum⟩` from `Submodule.mem_sup.mp hg`. Establish `hHw : H w = h0 • w`. Establish `e : H w - h0 • w = h0 • w' - H w'`.

Establish `h` using `congrArg H hsum`. Rewrite `h` using `[map_add, Hg0, ← hsum, smul_add]`. Rewrite using `[sub_eq_sub_iff_add_eq_add, h, add_comm]`. Establish `h1 : H w - h0 • w ∈ LinearMap.ker F` using `sub_mem (Hmem _ hWs w hw) (Submodule.smul_mem _ _ hw)`. Establish `h2' : H w - h0 • w ∈ W'`.

Rewrite using `[e]`. Conclude with `sub_mem (Submodule.smul_mem _ _ hw') (Hmem _ hW's w' hw')`. Conclude with `sub_eq_zero.mp ((Submodule.mem_bot K).mp (hC.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h1, h2'⟩)))`. Take `⟨r, hr⟩` from `key w hHw`. Establish `hr0 : r = 0`.

Establish `hFw : F w = 0` using `LinearMap.mem_ker.mp hw`. Rewrite `hFw` using `[hr, map_smul]`. Conclude with `(smul_eq_zero.mp hFw).resolve_right hne`. Establish `hg0W' : g0 ∈ W'`. Rewrite using `[← hsum, hr, hr0, zero_smul, zero_add]`.

Conclude with `hw'`. Establish `hbot` using `hC.inf_eq_bot`. Rewrite `hbot` using `[cycle W' hW's hg0W', inf_top_eq]`. Then use the resulting hypothesis.
-/
theorem equivariant_injective_of_cyclic (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K G V : Type} [Field K] [CharZero K]
    [AddCommGroup G] [Module K G] [FiniteDimensional K G] [AddCommGroup V] [Module K V]
    (EG : GLOps n K G) (hEG : IsGLRep EG) (E : GLOps n K V) (lam : Fin n → ℤ) (g0 : G) (hg0 : IsHWV EG lam g0)
    (hcyc : cyclicSubmodule EG g0 = ⊤) (F : G →ₗ[K] V) (hF : IsEquivariantMap EG E F) (hne : F g0 ≠ 0) :
    LinearMap.ker F = ⊥ := by
  classical
  have hEG0 := hEG
  obtain ⟨hcomm, -, -⟩ := hEG0
  obtain ⟨-, hg0w, hg0r⟩ := hg0
  have wt : ∀ (μ : Fin n → ℤ) (x : G), x ∈ weightSp EG μ ↔ ∀ a, EG a a x = ((μ a : ℤ) : K) • x := by
    intro μ x
    simp [weightSp, sub_eq_zero]
  have hlam := (wt lam g0).mp hg0w
  have comm : ∀ a b c d (y : G), EG c d (EG a b y) =
      EG a b (EG c d y) + ((if d = a then EG c b y else 0) - (if b = c then EG a d y else 0)) := by
    intro a b c d y
    have h' : EG c d (EG a b y) - EG a b (EG c d y) =
        (if d = a then EG c b y else 0) - (if b = c then EG a d y else 0) := by
      have h := LinearMap.congr_fun (hcomm c d a b) y
      split_ifs at h ⊢ <;> simpa using h
    exact sub_eq_iff_eq_add'.mp h'
  obtain ⟨L, hL⟩ : ∃ L : Submonoid (Module.End K G),
      L = Submonoid.closure {x | ∃ a b : Fin n, b < a ∧ x = EG a b} := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Submodule K G, N = Submodule.span K {x | ∃ l ∈ L, x = l g0} := ⟨_, rfl⟩
  have lowL : ∀ a b : Fin n, b < a → EG a b ∈ L := fun a b h => by
    rw [hL]; exact Submonoid.subset_closure ⟨a, b, h, rfl⟩
  have gen_mem : ∀ l ∈ L, l g0 ∈ N := fun l hl => by
    rw [hN]; exact Submodule.subset_span ⟨l, hl, rfl⟩
  have g0N : g0 ∈ N := by simpa using gen_mem 1 L.one_mem
  have low_mem : ∀ a b : Fin n, b < a → N ≤ N.comap (EG a b) := by
    intro a b hab
    refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hl, rfl⟩
    exact gen_mem _ (L.mul_mem (lowL a b hab) hl)
  have all_gen : ∀ l ∈ L, ∀ c d, EG c d (l g0) ∈ N := by
    intro l hl
    rw [hL] at hl
    induction hl using Submonoid.closure_induction_left with
    | one =>
      intro c d
      show EG c d g0 ∈ N
      rcases lt_trichotomy c d with h | h | h
      · rw [hg0r c d h]; exact N.zero_mem
      · rw [h, hlam d]; exact N.smul_mem _ g0N
      · exact gen_mem _ (lowL c d h)
    | mul_left s hs l _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hs
      intro c d
      show EG c d (EG a b (l g0)) ∈ N
      rw [comm a b c d (l g0)]
      refine N.add_mem (low_mem a b hab (ih c d)) (N.sub_mem ?_ ?_) <;>
        split_ifs <;> first | exact ih _ _ | exact N.zero_mem
  have all_mem : ∀ c d, ∀ x ∈ N, EG c d x ∈ N := by
    intro c d
    have hle : N ≤ N.comap (EG c d) := by
      refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨l, hl, rfl⟩
      exact all_gen l hl c d
    exact fun x hx => hle hx
  have umonS : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) →
      ∀ u ∈ Umon EG, ∀ x ∈ S, u x ∈ S := by
    intro S hS u hu
    have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => EG ab.1 ab.2) := hu
    clear hu
    induction hu' using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      exact fun y hy => hS a b y hy
    | one => exact fun y hy => hy
    | mul x y _ _ ihx ihy => exact fun z hz => ihx _ (ihy z hz)
  have cycle : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → g0 ∈ S → S = ⊤ := by
    intro S hS hg
    rw [eq_top_iff, ← hcyc]
    unfold cyclicSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact umonS S hS u hu g0 hg
  have Ntop : N = ⊤ := cycle N all_mem g0N
  obtain ⟨H, hH⟩ : ∃ H : Module.End K G, H = ∑ c : Fin n, ((c : ℕ) : K) • EG c c := ⟨_, rfl⟩
  have hHapp : ∀ y, H y = ∑ c : Fin n, ((c : ℕ) : K) • EG c c y := by
    intro y
    rw [hH]
    simp
  obtain ⟨h0, hh0⟩ : ∃ h0 : K, h0 = ∑ c : Fin n, ((c : ℕ) : K) * ((lam c : ℤ) : K) := ⟨_, rfl⟩
  have Hg0 : H g0 = h0 • g0 := by
    rw [hHapp, hh0, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hlam c, smul_smul]
  have Hstep : ∀ (a b : Fin n) (y : G) (t : K), H y = t • y →
      H (EG a b y) = (t + (((a : ℕ) : K) - ((b : ℕ) : K))) • EG a b y := by
    intro a b y t hy
    have e1 : ∑ c : Fin n, ((c : ℕ) : K) • EG a b (EG c c y) = EG a b (H y) := by
      rw [hHapp, map_sum]
      simp only [map_smul]
    have e2 : ∑ c : Fin n, ((c : ℕ) : K) • (if c = a then EG c b y else 0) =
        ((a : ℕ) : K) • EG a b y := by
      simp [smul_ite]
    have e3 : ∑ c : Fin n, ((c : ℕ) : K) • (if b = c then EG a c y else 0) =
        ((b : ℕ) : K) • EG a b y := by
      simp [smul_ite]
    rw [hHapp]
    simp only [comm a b, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3,
      hy, map_smul]
    rw [add_smul, sub_smul]
  have alt : ∀ l ∈ L, (∃ r : K, l g0 = r • g0) ∨
      ∃ k : ℕ, 0 < k ∧ H (l g0) = (h0 + (k : K)) • l g0 := by
    intro l hl
    rw [hL] at hl
    induction hl using Submonoid.closure_induction_left with
    | one => exact Or.inl ⟨1, by simp⟩
    | mul_left s hs l _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hs
      have hab' : (b : ℕ) < (a : ℕ) := hab
      have hcast : ((a : ℕ) : K) - ((b : ℕ) : K) = (((a : ℕ) - (b : ℕ) : ℕ) : K) := by
        rw [Nat.cast_sub hab'.le]
      right
      rcases ih with ⟨r, hr⟩ | ⟨k, hk0, hHk⟩
      · refine ⟨(a : ℕ) - (b : ℕ), by omega, ?_⟩
        show H (EG a b (l g0)) = _ • EG a b (l g0)
        rw [hr, map_smul, map_smul, Hstep a b g0 h0 Hg0, hcast]
        exact smul_comm _ _ _
      · refine ⟨k + ((a : ℕ) - (b : ℕ)), by omega, ?_⟩
        show H (EG a b (l g0)) = _ • EG a b (l g0)
        rw [Hstep a b _ _ hHk, hcast, Nat.cast_add, add_assoc]
  have key : ∀ w : G, H w = h0 • w → ∃ r : K, w = r • g0 := by
    intro w hw
    have hle : N ≤ Submodule.span K {g0} ⊔ ⨆ (μ : K) (_ : μ ≠ h0), Module.End.eigenspace H μ := by
      refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨l, hl, rfl⟩
      rcases alt l hl with ⟨r, hr⟩ | ⟨k, hk, hHk⟩
      · rw [hr]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self g0))
      · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (h0 + (k : K))
          (Submodule.mem_iSup_of_mem ?_ ?_))
        · intro h
          have : k = 0 := by simpa using h
          omega
        · exact Module.End.mem_eigenspace_iff.mpr hHk
    have hwN : w ∈ N := by rw [Ntop]; exact Submodule.mem_top
    obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp (hle hwN)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hz0 : z ∈ Module.End.eigenspace H h0 := by
      rw [Module.End.mem_eigenspace_iff]
      rw [map_add, map_smul, Hg0, smul_add, smul_comm h0 r g0] at hw
      exact add_left_cancel hw
    have hz' : z = 0 := (Submodule.mem_bot K).mp
      ((Module.End.eigenspaces_iSupIndep H h0).le_bot (Submodule.mem_inf.mpr ⟨hz0, hz⟩))
    exact ⟨r, by rw [hz', add_zero]⟩
  have hWs : ∀ a b, ∀ x ∈ LinearMap.ker F, EG a b x ∈ LinearMap.ker F := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hF a b x, hx, map_zero]
  obtain ⟨W', hC, hW's⟩ := h2 K G n EG hEG (LinearMap.ker F) hWs
  have Hmem : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → ∀ x ∈ S, H x ∈ S := by
    intro S hS x hx
    rw [hHapp]
    exact S.sum_mem fun c _ => S.smul_mem _ (hS c c x hx)
  have hg : g0 ∈ LinearMap.ker F ⊔ W' := by rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.mp hg
  have hHw : H w = h0 • w := by
    have e : H w - h0 • w = h0 • w' - H w' := by
      have h := congrArg H hsum
      rw [map_add, Hg0, ← hsum, smul_add] at h
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have h1 : H w - h0 • w ∈ LinearMap.ker F := sub_mem (Hmem _ hWs w hw) (Submodule.smul_mem _ _ hw)
    have h2' : H w - h0 • w ∈ W' := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hw') (Hmem _ hW's w' hw')
    exact sub_eq_zero.mp ((Submodule.mem_bot K).mp (hC.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h1, h2'⟩)))
  obtain ⟨r, hr⟩ := key w hHw
  have hr0 : r = 0 := by
    have hFw : F w = 0 := LinearMap.mem_ker.mp hw
    rw [hr, map_smul] at hFw
    exact (smul_eq_zero.mp hFw).resolve_right hne
  have hg0W' : g0 ∈ W' := by
    rw [← hsum, hr, hr0, zero_smul, zero_add]
    exact hw'
  have hbot := hC.inf_eq_bot
  rwa [cycle W' hW's hg0W', inf_top_eq] at hbot

end Formalism.MainNotions.G.GLWeightTheory
