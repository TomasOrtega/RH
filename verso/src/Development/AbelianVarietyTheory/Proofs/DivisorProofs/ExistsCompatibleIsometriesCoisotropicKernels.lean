import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeTransversalIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicModStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Conclude with `⟨k • e, mul_smul n k e⟩`.
-/
theorem nsmul_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] {n m : ℕ} (h : n ∣ m) (e : M) : ∃ e', m • e = n • e' := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k • e, mul_smul n k e⟩

/- English proof (translation)
Use `⟨fun x => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨a, e, he⟩` from `hy.1 x`. Conclude with `⟨G.symm a, e, by simpa using he⟩`. Use `hy.2 (G a) fun b hb => by` as an intermediate fact. Establish `h1` using `ha (G.symm b) (by simpa using hb)`.

Rewrite `h1` using `[← hG a (G.symm b), G.apply_symm_apply]`. Then use the resulting hypothesis. Conclude with `this`.
-/
theorem Cois.comp_isometry {y : D.La →ₗ[𝓞 E] X} {n : ℕ} (hy : Cois D y n) (G : D.La ≃ₗ[𝓞 E] D.La)
    (hG : ∀ a b, D.EF (G a) (G b) = D.EF a b) : Cois D (y.comp G.toLinearMap) n := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨a, e, he⟩ := hy.1 x
    exact ⟨G.symm a, e, by simpa using he⟩
  · have := hy.2 (G a) fun b hb => by
      have h1 := ha (G.symm b) (by simpa using hb)
      rwa [← hG a (G.symm b), G.apply_symm_apply] at h1
    exact this

/- English proof (translation)
Take `⟨e₀, he₀⟩` from `h a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩`. Conclude with `⟨e + e₀, by rw [he₀, he, smul_add]⟩`. Introduce and unpack `⟨e, he⟩`.

Conclude with `⟨e - e₀, by rw [smul_sub, ← he, he₀]; abel⟩`.
-/
theorem ker_iff_of_congr {f f' : D.La →ₗ[𝓞 E] X} {n : ℕ} (h : ∀ a, ∃ e, f' a = f a + n • e) (a : D.La) :
    (∃ e, f a = n • e) ↔ ∃ e, f' a = n • e := by
  obtain ⟨e₀, he₀⟩ := h a
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e + e₀, by rw [he₀, he, smul_add]⟩
  · rintro ⟨e, he⟩
    exact ⟨e - e₀, by rw [smul_sub, ← he, he₀]; abel⟩

/- English proof (translation)
Introduce `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`. Take `⟨c, e', hc⟩` from `hon x`. Establish `h1 : ∃ e, f (a - n • c) = n' • e` using `⟨-(n • e'), by`.

Rewrite using `[map_sub, map_nsmul, hx, hc, smul_add, smul_neg, smul_comm n' n e']`. Use the proof step `abel⟩`. Take `⟨b, hb, e, he⟩` from `(hk _).1 h1`. Take `⟨e'', he''⟩` from `nsmul_eq_nsmul_of_dvd hd e`. Use `⟨b, hb, c + e'', ?_⟩` and prove the remaining obligations.

Rewrite `he` using `[sub_eq_iff_eq_add]`. Rewrite using `[he, smul_add, ← he'']`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨b, hb, e, rfl⟩`. Take `⟨e', he'⟩` from `(hk b).2 ⟨b, hb, 0, by simp⟩`.

Take `⟨e'', he''⟩` from `nsmul_eq_nsmul_of_dvd hd e'`. Conclude with `⟨e'' + f e, by rw [map_add, map_nsmul, he', he'', smul_add]⟩`.
-/
theorem KerIs.of_dvd {f : D.La →ₗ[𝓞 E] X} {Z : Submodule (𝓞 E) D.La} {n n' : ℕ} (hk : KerIs D f Z n')
    (hon : ∀ x, ∃ a e, f a = x + n' • e) (hd : n ∣ n') : KerIs D f Z n := by
  intro a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, e', hc⟩ := hon x
    have h1 : ∃ e, f (a - n • c) = n' • e := ⟨-(n • e'), by
      rw [map_sub, map_nsmul, hx, hc, smul_add, smul_neg, smul_comm n' n e']; abel⟩
    obtain ⟨b, hb, e, he⟩ := (hk _).1 h1
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e
    refine ⟨b, hb, c + e'', ?_⟩
    rw [sub_eq_iff_eq_add] at he
    rw [he, smul_add, ← he'']; abel
  · rintro ⟨b, hb, e, rfl⟩
    obtain ⟨e', he'⟩ := (hk b).2 ⟨b, hb, 0, by simp⟩
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e'
    exact ⟨e'' + f e, by rw [map_add, map_nsmul, he', he'', smul_add]⟩

/- English proof (translation)
Take `⟨Z'', hop'', hon⟩` from `GlobalTheory.T.exists_opposite_transversal_isotropic D f n hn hc Z FinalForm hop hrk`. Take `⟨h, hi, hN, hk'⟩` from `GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D f n N' hn hd hc Z Z'' hop'' hrk hk hon`. Conclude with `⟨h, hi, hN, hk'⟩`.
-/
theorem exists_step [Module.Free ℤ X] [Module.Finite ℤ X] {Z FinalForm : Submodule (𝓞 E) D.La} (hop : IsOpp D Z FinalForm)
    (hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (f : D.La →ₗ[𝓞 E] X) {n N' : ℕ} (hn : 0 < n)
    (hd : N' ∣ n) (hc : Cois D f n) (hk : KerIs D f Z N') :
    ∃ h : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (h a) (h b) = D.EF a b) ∧ (∀ a, ∃ e, h a = a + N' • e) ∧
      KerIs D (f.comp h.toLinearMap) Z n := by
  obtain ⟨Z'', hop'', hon⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D f n hn hc Z FinalForm hop hrk
  obtain ⟨h, hi, hN, hk'⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D f n N' hn hd hc Z Z'' hop'' hrk hk hon
  exact ⟨h, hi, hN, hk'⟩

def levelSeq (N j : ℕ) : ℕ := N * (j + 1).factorial

/- English proof (translation)
The claim follows from `Nat.mul_pos hN (Nat.factorial_pos _)`.
-/
theorem levelSeq_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < levelSeq N j := Nat.mul_pos hN (Nat.factorial_pos _)

/- English proof (translation)
Unfold `levelSeq`. Rewrite using `[Nat.factorial_succ (j + 1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levelSeq_succ (N j : ℕ) : levelSeq N (j + 1) = levelSeq N j * (j + 2) := by
  unfold levelSeq; rw [Nat.factorial_succ (j + 1)]; ring

/- English proof (translation)
The claim follows from `Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial (by omega))`.
-/
theorem levelSeq_dvd (N : ℕ) {i j : ℕ} (h : i ≤ j) : levelSeq N i ∣ levelSeq N j :=
  Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial (by omega))

/- English proof (translation)
The claim follows from `Dvd.dvd.mul_left (Nat.dvd_factorial hn (Nat.le_succ n)) N`.
-/
theorem dvd_levelSeq (N : ℕ) {n : ℕ} (hn : 0 < n) : n ∣ levelSeq N n :=
  Dvd.dvd.mul_left (Nat.dvd_factorial hn (Nat.le_succ n)) N

/- English proof (translation)
Simplify using `[levelSeq]`.
-/
theorem levelSeq_zero (N : ℕ) : levelSeq N 0 = N := by simp [levelSeq]

def GoodAt (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (N n : ℕ) (G : D.La ≃ₗ[𝓞 E] D.La) : Prop :=
  (∀ a b, D.EF (G a) (G b) = D.EF a b) ∧ (∀ a, ∃ e, G a = a + N • e) ∧ KerIs D (y.comp G.toLinearMap) Z n

def iterSeq {α : Type} (x₀ : α) (f : ℕ → α → α) (j : ℕ) : α := Nat.rec (motive := fun _ => α) x₀ f j

/- English proof (translation)
Introduce `E _ _ _ H D X _ _ _ _ y hc hy hr N hN`. Take `⟨Z₀, hZ₀, hrk₀⟩` from `GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le D _ hr`. Take `⟨Z₀', hop₀⟩` from `GlobalTheory.T.exists_oppositeIsotropicPair D Z₀ hZ₀`. Take `⟨Z₁', hop₁, hon₁⟩` from `GlobalTheory.T.exists_opposite_transversal_isotropic D (y N) N hN (hc N hN) Z₀ Z₀' hop₀ hrk₀`. Take `⟨g₀, hg₀, -, hk₀⟩` from `GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D (y N) N 1 hN (one_dvd N) (hc N hN) Z₀ Z₁' hop₁ hrk₀ (fun a => ⟨fun _ => ⟨0, zero_mem _, a, by simp⟩, fun _ => ⟨y N a, by simp⟩⟩) hon₁`.

Use `set Z := Z₀.map (g₀ : D.La →ₗ[𝓞 E] D.La) with hZdef`. Establish `memZ : ∀ x, x ∈ Z ↔ g₀.symm x ∈ Z₀` using `fun x => Submodule.mem_map_equiv Z₀`. Establish `memP : ∀ x, x ∈ perp D Z ↔ g₀.symm x ∈ perp D Z₀`. Introduce `x`. Rewrite using `[mem_perp, mem_perp]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx z hz`. Use `hx (g₀ z) ((memZ _).2 (by simpa using hz))` as an intermediate fact. Rewrite using `[← hg₀ (g₀.symm x) z, g₀.apply_symm_apply]` and apply the resulting hypothesis. Introduce `hx z hz`.

Use `hx _ ((memZ z).1 hz)` as an intermediate fact. Rewrite `this` using `[← hg₀ (g₀.symm x) (g₀.symm z), g₀.apply_symm_apply, g₀.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hZ : IsIsoSat D Z`. Use `⟨fun z hz => (memP z).2 (hZ₀.1 ((memZ z).1 hz)), fun n x hn hx => (memZ x).2 ?_⟩` and prove the remaining obligations. Use `(memZ _).1 hx` as an intermediate fact.

Rewrite `this` using `[map_nsmul]`. Conclude with `hZ₀.2 n _ hn this`. Establish `hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X`. Rewrite using `[← hrk₀]`. Conclude with `(g₀.submoduleMap Z₀).finrank_eq.symm`.

Take `⟨FinalForm, hop⟩` from `GlobalTheory.T.exists_oppositeIsotropicPair D Z hZ`. Establish `hbase : KerIs D (y N) Z N`. Introduce `a`. Establish `h1` using `hk₀ (g₀.symm a)`. Rewrite `h1` using `[g₀.apply_symm_apply]`.

Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, e, he⟩`. Use `⟨g₀ b, (memP _).2 (by rwa [g₀.symm_apply_apply]), g₀ e, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← g₀.apply_symm_apply a, he]`.

Rewrite using `[map_add, map_nsmul]`. Introduce and unpack `⟨b, hb, e, rfl⟩`. Conclude with `⟨g₀.symm b, (memP b).1 hb, g₀.symm e, by rw [map_add, map_nsmul]⟩`. Establish `hstep : ∀ j (G : D.La ≃ₗ[𝓞 E] D.La), GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) G → ∃ G' : D.La ≃ₗ[𝓞 E] D.La, GoodAt D (y (levelSeq N (j + 1))) Z N (levelSeq N (j + 1)) G' ∧ ∀ a, ∃ e, G' a = G a + levelSeq N j • e`. Introduce and unpack `j G ⟨hGi, hGN, hGk⟩`.

Establish `hcong : ∀ a, ∃ e, ((y (levelSeq N (j + 1))).comp G.toLinearMap) a = ((y (levelSeq N j)).comp G.toLinearMap) a + levelSeq N j • e`. Introduce `a`. Rewrite using `[levelSeq_succ]`. Conclude with `hy (levelSeq N j) (j + 2) (levelSeq_pos hN j) (by omega) (G a)`. Establish `hk : KerIs D ((y (levelSeq N (j + 1))).comp G.toLinearMap) Z (levelSeq N j)` using `fun a => (ker_iff_of_congr hcong a).symm.trans (hGk a)`.

Apply the tactic sequence `obtain ⟨h, hi, hN', hk'⟩ := exists_step hop hrk ((y (levelSeq N (j + 1))).comp G.toLinearMap) (levelSeq_pos hN (j + 1)) (levelSeq_dvd N (Nat.le_succ j)) ((hc _ (levelSeq_pos hN _)).comp_isometry G hGi) hk`. Use `⟨h.trans G, ⟨fun a b => ?_, fun a => ?_, fun a => hk' a⟩, fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply]`. Rewrite using `[hGi, hi]`. Take `⟨e, he⟩` from `hN' a`.

Take `⟨e₁, he₁⟩` from `hGN a`. Take `⟨e₂, he₂⟩` from `nsmul_eq_nsmul_of_dvd (Dvd.intro _ rfl : N ∣ levelSeq N j) (G e)`. Conclude with `⟨e₁ + e₂, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul, he₁, he₂, smul_add, add_assoc]⟩`. Take `⟨e, he⟩` from `hN' a`. Conclude with `⟨G e, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul]⟩`.

Use `choose! F hF hFc using hstep`. Take `⟨S, hS0, hSs⟩ : ∃ S : ℕ → D.La ≃ₗ[𝓞 E] D.La, S 0 = LinearEquiv.refl _ _ ∧ ∀ j, S (j + 1) = F j (S j)` from `⟨iterSeq (LinearEquiv.refl _ _) F, rfl, fun _ => rfl⟩`. Establish `hgood : ∀ j, GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) (S j)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[hS0, levelSeq_zero]`. Conclude with `⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩, fun a => hbase a⟩`. Consider the case `succ j ih => rw [hSs]`. Conclude with `hF j (S j) ih`.

Establish `hc1 : ∀ j a, ∃ e, S (j + 1) a = S j a + levelSeq N j • e` using `fun j a => by`. Rewrite using `[hSs]`. Conclude with `hFc j (S j) (hgood j) a`. Establish `hck : ∀ i k a, ∃ e, S (i + k) a = S i a + levelSeq N i • e`. Introduce `i k`.

Proceed by induction on `k with`. Consider the case `zero => intro a; exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Introduce `a`. Take `⟨e, he⟩` from `ih a`.

Take `⟨e₁, he₁⟩` from `hc1 (i + k) a`. Take `⟨e₂, he₂⟩` from `nsmul_eq_nsmul_of_dvd (levelSeq_dvd N (Nat.le_add_right i k)) e₁`. Conclude with `⟨e + e₂, by rw [← Nat.add_assoc, he₁, he, he₂, smul_add, add_assoc]⟩`. Use `⟨Z, hZ, hrk, S, fun n => (hgood n).1, fun n m hn hm a => ?_, fun n => (hgood n).2.1, fun n hn a => ?_⟩` and prove the remaining obligations. Establish `hle : n ≤ n * m` using `Nat.le_mul_of_pos_right n hm`.

Rewrite using `[← Nat.add_sub_of_le hle]`. Take `⟨e, he⟩` from `hck n (n * m - n) a`. Take `⟨e', he'⟩` from `nsmul_eq_nsmul_of_dvd (dvd_levelSeq N hn) e`. Conclude with `⟨e', by rw [he, he']⟩`. Establish `hg` using `hgood n`.

Apply the tactic sequence `have hon := ((hc _ (levelSeq_pos hN n)).comp_isometry (S n) hg.1).1`. Establish `hkn` using `hg.2.2.of_dvd hon (dvd_levelSeq N hn)`. Take `⟨k, hk⟩` from `dvd_levelSeq N hn`. Establish `hkpos : 0 < k`. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases.

Rewrite `hk` using `[h0, mul_zero]`. Conclude with `absurd hk (levelSeq_pos hN n).ne'`. Conclude with `h0`. Establish `hcong : ∀ a, ∃ e, ((y (levelSeq N n)).comp (S n).toLinearMap) a = ((y n).comp (S n).toLinearMap) a + n • e`. Introduce `a`.

Rewrite using `[hk]`. Conclude with `hy n k hn hkpos (S n a)`. Conclude with `(ker_iff_of_congr hcong a).trans (hkn a)`.
-/
theorem exists_compatible_isometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y hc hy hr N hN
  classical
  obtain ⟨Z₀, hZ₀, hrk₀⟩ := GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le D _ hr
  obtain ⟨Z₀', hop₀⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z₀ hZ₀
  obtain ⟨Z₁', hop₁, hon₁⟩ := GlobalTheory.T.exists_opposite_transversal_isotropic D (y N) N hN (hc N hN) Z₀ Z₀' hop₀ hrk₀
  obtain ⟨g₀, hg₀, -, hk₀⟩ := GlobalTheory.T.exists_isometry_kernel_coisotropic_mod D (y N) N 1 hN (one_dvd N) (hc N hN) Z₀ Z₁' hop₁ hrk₀
    (fun a => ⟨fun _ => ⟨0, zero_mem _, a, by simp⟩, fun _ => ⟨y N a, by simp⟩⟩) hon₁
  set Z := Z₀.map (g₀ : D.La →ₗ[𝓞 E] D.La) with hZdef
  have memZ : ∀ x, x ∈ Z ↔ g₀.symm x ∈ Z₀ := fun x => Submodule.mem_map_equiv Z₀
  have memP : ∀ x, x ∈ perp D Z ↔ g₀.symm x ∈ perp D Z₀ := by
    intro x
    rw [mem_perp, mem_perp]
    constructor
    · intro hx z hz
      have := hx (g₀ z) ((memZ _).2 (by simpa using hz))
      rwa [← hg₀ (g₀.symm x) z, g₀.apply_symm_apply]
    · intro hx z hz
      have := hx _ ((memZ z).1 hz)
      rwa [← hg₀ (g₀.symm x) (g₀.symm z), g₀.apply_symm_apply, g₀.apply_symm_apply] at this
  have hZ : IsIsoSat D Z := by
    refine ⟨fun z hz => (memP z).2 (hZ₀.1 ((memZ z).1 hz)), fun n x hn hx => (memZ x).2 ?_⟩
    have := (memZ _).1 hx
    rw [map_nsmul] at this
    exact hZ₀.2 n _ hn this
  have hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X := by
    rw [← hrk₀]; exact (g₀.submoduleMap Z₀).finrank_eq.symm
  obtain ⟨FinalForm, hop⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z hZ
  have hbase : KerIs D (y N) Z N := by
    intro a
    have h1 := hk₀ (g₀.symm a)
    rw [g₀.apply_symm_apply] at h1
    rw [h1]
    constructor
    · rintro ⟨b, hb, e, he⟩
      refine ⟨g₀ b, (memP _).2 (by rwa [g₀.symm_apply_apply]), g₀ e, ?_⟩
      conv_lhs => rw [← g₀.apply_symm_apply a, he]
      rw [map_add, map_nsmul]
    · rintro ⟨b, hb, e, rfl⟩
      exact ⟨g₀.symm b, (memP b).1 hb, g₀.symm e, by rw [map_add, map_nsmul]⟩
  have hstep : ∀ j (G : D.La ≃ₗ[𝓞 E] D.La), GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) G →
      ∃ G' : D.La ≃ₗ[𝓞 E] D.La, GoodAt D (y (levelSeq N (j + 1))) Z N (levelSeq N (j + 1)) G' ∧
        ∀ a, ∃ e, G' a = G a + levelSeq N j • e := by
    rintro j G ⟨hGi, hGN, hGk⟩
    have hcong : ∀ a, ∃ e, ((y (levelSeq N (j + 1))).comp G.toLinearMap) a =
        ((y (levelSeq N j)).comp G.toLinearMap) a + levelSeq N j • e := by
      intro a
      rw [levelSeq_succ]
      exact hy (levelSeq N j) (j + 2) (levelSeq_pos hN j) (by omega) (G a)
    have hk : KerIs D ((y (levelSeq N (j + 1))).comp G.toLinearMap) Z (levelSeq N j) := fun a =>
      (ker_iff_of_congr hcong a).symm.trans (hGk a)
    obtain ⟨h, hi, hN', hk'⟩ := exists_step hop hrk ((y (levelSeq N (j + 1))).comp G.toLinearMap)
      (levelSeq_pos hN (j + 1)) (levelSeq_dvd N (Nat.le_succ j)) ((hc _ (levelSeq_pos hN _)).comp_isometry G hGi) hk
    refine ⟨h.trans G, ⟨fun a b => ?_, fun a => ?_, fun a => hk' a⟩, fun a => ?_⟩
    · simp only [LinearEquiv.trans_apply]; rw [hGi, hi]
    · obtain ⟨e, he⟩ := hN' a
      obtain ⟨e₁, he₁⟩ := hGN a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (Dvd.intro _ rfl : N ∣ levelSeq N j) (G e)
      exact ⟨e₁ + e₂, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul, he₁, he₂, smul_add, add_assoc]⟩
    · obtain ⟨e, he⟩ := hN' a
      exact ⟨G e, by rw [LinearEquiv.trans_apply, he, map_add, map_nsmul]⟩
  choose! F hF hFc using hstep
  obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → D.La ≃ₗ[𝓞 E] D.La, S 0 = LinearEquiv.refl _ _ ∧ ∀ j, S (j + 1) = F j (S j) :=
    ⟨iterSeq (LinearEquiv.refl _ _) F, rfl, fun _ => rfl⟩
  have hgood : ∀ j, GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) (S j) := by
    intro j
    induction j with
    | zero =>
      rw [hS0, levelSeq_zero]
      exact ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩, fun a => hbase a⟩
    | succ j ih => rw [hSs]; exact hF j (S j) ih
  have hc1 : ∀ j a, ∃ e, S (j + 1) a = S j a + levelSeq N j • e := fun j a => by
    rw [hSs]; exact hFc j (S j) (hgood j) a
  have hck : ∀ i k a, ∃ e, S (i + k) a = S i a + levelSeq N i • e := by
    intro i k
    induction k with
    | zero => intro a; exact ⟨0, by simp⟩
    | succ k ih =>
      intro a
      obtain ⟨e, he⟩ := ih a
      obtain ⟨e₁, he₁⟩ := hc1 (i + k) a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (levelSeq_dvd N (Nat.le_add_right i k)) e₁
      exact ⟨e + e₂, by rw [← Nat.add_assoc, he₁, he, he₂, smul_add, add_assoc]⟩
  refine ⟨Z, hZ, hrk, S, fun n => (hgood n).1, fun n m hn hm a => ?_, fun n => (hgood n).2.1, fun n hn a => ?_⟩
  · have hle : n ≤ n * m := Nat.le_mul_of_pos_right n hm
    rw [← Nat.add_sub_of_le hle]
    obtain ⟨e, he⟩ := hck n (n * m - n) a
    obtain ⟨e', he'⟩ := nsmul_eq_nsmul_of_dvd (dvd_levelSeq N hn) e
    exact ⟨e', by rw [he, he']⟩
  · have hg := hgood n
    have hon := ((hc _ (levelSeq_pos hN n)).comp_isometry (S n) hg.1).1
    have hkn := hg.2.2.of_dvd hon (dvd_levelSeq N hn)
    obtain ⟨k, hk⟩ := dvd_levelSeq N hn
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; exact absurd hk (levelSeq_pos hN n).ne'
      · exact h0
    have hcong : ∀ a, ∃ e, ((y (levelSeq N n)).comp (S n).toLinearMap) a =
        ((y n).comp (S n).toLinearMap) a + n • e := by
      intro a
      rw [hk]
      exact hy n k hn hkpos (S n a)
    exact (ker_iff_of_congr hcong a).trans (hkn a)

end GlobalTheory.LowFilt
