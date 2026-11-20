import Development.EtaleCohomology.TateTwists.KumAddPf
import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue
import Development.EtaleCohomology.TateTwists.EtaleCochainExistsOfNaturalEvaluation
import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationCoboundaryFormula
import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationLinear

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.KMC

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Conclude with `⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩`.
-/
theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Use `choose R hR hQ using fun V (g : V ⟶ U) (hg : S.arrows g) => hb V g (hP V g hg)`. Use `⟨Sieve.bind S.arrows (fun V g hg => R V g hg), Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩` and prove the remaining obligations. Introduce and unpack `W h ⟨V, k, g, hg, hk, rfl⟩`. Conclude with `hQ V g hg W k hk`.
-/
theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hb : ∀ V (g : V ⟶ U), P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose R hR hQ using fun V (g : V ⟶ U) (hg : S.arrows g) => hb V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W h ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg W k hk

/- English proof (translation)
Use `ext`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Both sides reduce to the same expression.
-/
theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom a =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a) := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rfl

/- English proof (translation)
Simplify using `using hq.map g.appTop.hom`.
-/
theorem unit_q {V U : Scheme.{0}} (q : ℕ) (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp [Sec.res]

/- English proof (translation)
Simplify using `only [Sec.res, Sec.map]`. Conclude with `congrArg (fun f => f.hom s) (φ.hom.naturality g.op).symm`.
-/
theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => f.hom s) (φ.hom.naturality g.op).symm

variable (q : ℕ)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v w h`. Simplify using `at h`. Rewrite using `[Units.ext h]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `v w h`. Establish `hu : IsUnit (ζ.1 ^ n * v)`. Apply `isUnit_of_mul_isUnit_right (x := ζ.1)` to reduce the goal to its premises.

Rewrite using `[← mul_assoc, ← pow_succ']`. Rewrite using `[← h]`. Conclude with `w.isUnit`. Rewrite using `[hk.2 V ζ hu.unit w (by rw [h, hu.unit_spec, pow_succ', mul_assoc]), ih v hu.unit hu.unit_spec]`. Rewrite using `[succ_nsmul]`.

Normalize the expressions using the abelian group laws.
-/
theorem kumT_pow (hk : IsKum q (kumT q)) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ∀ (n : ℕ) (v w : (Γ(V, ⊤))ˣ), (w : Γ(V, ⊤)) = ζ.1 ^ n * v → kumT q V w = kumT q V v + n • resGen 1 ζ := by
  intro n
  induction n with
  | zero => intro v w h; simp at h; rw [Units.ext h]; simp
  | succ n ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ n * v) := by
      apply isUnit_of_mul_isUnit_right (x := ζ.1); rw [← mul_assoc, ← pow_succ']; rw [← h]; exact w.isUnit
    rw [hk.2 V ζ hu.unit w (by rw [h, hu.unit_spec, pow_succ', mul_assoc]), ih v hu.unit hu.unit_spec]
    rw [succ_nsmul]; abel

noncomputable def D (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) V :=
  kumT q V (a * b) - kumT q V a - kumT q V b

/- English proof (translation)
Simplify using `only [D, mul_comm a b]`. Normalize the expressions using the abelian group laws.
-/
theorem D_comm (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : D q V a b = D q V b a := by
  simp only [D, mul_comm a b]; abel

/- English proof (translation)
Simplify using `only [D, Sec.res, map_sub] at *`. Establish `h` using `hk.1 W V k`. Simplify using `only [Sec.res] at h`. Rewrite using `[h _ hq, h _ hq, h _ hq, map_mul]`.
-/
theorem D_res (hk : IsKum q (kumT q)) {W V : Scheme.{0}} (k : W ⟶ V) (hq : IsUnit (q : Γ(V, ⊤))) (a b : (Γ(V, ⊤))ˣ) :
    Sec.res k (D q V a b) = D q W (Units.map k.appTop.hom.toMonoidHom a) (Units.map k.appTop.hom.toMonoidHom b) := by
  simp only [D, Sec.res, map_sub] at *
  have h := hk.1 W V k
  simp only [Sec.res] at h
  rw [h _ hq, h _ hq, h _ hq, map_mul]

/- English proof (translation)
Apply `(hs _ _ V).1` to reduce the goal to its premises. Use `set c := a' * a⁻¹ with hcdef`. Establish `hc : c ^ q = 1` using `by rw [hcdef, mul_pow, h, inv_pow, mul_inv_cancel]`. Establish `hac : a' = c * a` using `by rw [hcdef, inv_mul_cancel_right]`. Use `loc_bind ((hp q V).1 hq) (fun W g hζ => ?_)` and prove the remaining obligations.

Take `⟨ζ⟩` from `hζ`. Use `loc_mono ((hp q W).2.2.1 ζ (g.appTop.hom c) (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one])) (fun W' k hn => ?_)` and prove the remaining obligations. Take `⟨n, hn⟩` from `hn`. Establish `hq' : IsUnit (q : Γ(V, ⊤))` using `hq`. Rewrite using `[D_res q hk (k ≫ g) hq, D_res q hk (k ≫ g) hq]`.

Simplify using `only [umap_comp]`. Use `set ζ'' : Prim q Γ(W', ⊤) := Prim.map k.appTop.hom ζ`. Use `set A := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a)`. Use `set A' := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a')`. Use `set B := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b)`.

Establish `key : (A' : Γ(W', ⊤)) = ζ''.1 ^ n * A`. Simplify using `only [A, A', ζ'', Prim.map, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hac, Units.val_mul, map_mul]`. Rewrite using `[hn]`. Unfold `D`. Rewrite using `[kumT_pow q hk ζ'' n (A * B) (A' * B) (by rw [Units.val_mul, Units.val_mul, key, mul_assoc]), kumT_pow q hk ζ'' n A A' key]`.

Normalize the expressions using the abelian group laws.
-/
theorem D_change (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b : (Γ(V, ⊤))ˣ) (h : a' ^ q = a ^ q) :
    D q V a' b = D q V a b := by
  apply (hs _ _ V).1
  set c := a' * a⁻¹ with hcdef
  have hc : c ^ q = 1 := by rw [hcdef, mul_pow, h, inv_pow, mul_inv_cancel]
  have hac : a' = c * a := by rw [hcdef, inv_mul_cancel_right]
  refine loc_bind ((hp q V).1 hq) (fun W g hζ => ?_)
  obtain ⟨ζ⟩ := hζ
  refine loc_mono ((hp q W).2.2.1 ζ (g.appTop.hom c) (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one])) (fun W' k hn => ?_)
  obtain ⟨n, hn⟩ := hn
  have hq' : IsUnit (q : Γ(V, ⊤)) := hq
  rw [D_res q hk (k ≫ g) hq, D_res q hk (k ≫ g) hq]
  simp only [umap_comp]
  set ζ'' : Prim q Γ(W', ⊤) := Prim.map k.appTop.hom ζ
  set A := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a)
  set A' := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a')
  set B := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b)
  have key : (A' : Γ(W', ⊤)) = ζ''.1 ^ n * A := by
    simp only [A, A', ζ'', Prim.map, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hac,
      Units.val_mul, map_mul]
    rw [hn]
  unfold D
  rw [kumT_pow q hk ζ'' n (A * B) (A' * B) (by rw [Units.val_mul, Units.val_mul, key, mul_assoc]),
    kumT_pow q hk ζ'' n A A' key]
  abel

/- English proof (translation)
Rewrite using `[D_change q hk hp hs hq a a' b' ha, D_comm, D_change q hk hp hs hq b b' a hb, D_comm]`.
-/
theorem D_change2 (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b b' : (Γ(V, ⊤))ˣ) (ha : a' ^ q = a ^ q) (hb : b' ^ q = b ^ q) :
    D q V a' b' = D q V a b := by
  rw [D_change q hk hp hs hq a a' b' ha, D_comm, D_change q hk hp hs hq b b' a hb, D_comm]

def KP {V : Scheme.{0}} (u v : (Γ(V, ⊤))ˣ) (Z : Sec ((res _ (tw q 1)).X 0) V) : Prop :=
  ∀ (W : Scheme.{0}) (k : W ⟶ V) (a b : (Γ(W, ⊤))ˣ), a ^ q = Units.map k.appTop.hom.toMonoidHom u →
    b ^ q = Units.map k.appTop.hom.toMonoidHom v → Sec.res k Z = D q W a b

/- English proof (translation)
Introduce `W' k' a b ha hb`. Rewrite using `[res_comp]`. Conclude with `hZ W' (k' ≫ k) a b (by rw [ha, umap_comp]) (by rw [hb, umap_comp])`.
-/
theorem KP_res {W V : Scheme.{0}} (k : W ⟶ V) {u v : (Γ(V, ⊤))ˣ} {Z : Sec ((res _ (tw q 1)).X 0) V}
    (hZ : KP q u v Z) : KP q (Units.map k.appTop.hom.toMonoidHom u) (Units.map k.appTop.hom.toMonoidHom v) (Sec.res k Z) := by
  intro W' k' a b ha hb
  rw [res_comp]
  exact hZ W' (k' ≫ k) a b (by rw [ha, umap_comp]) (by rw [hb, umap_comp])

/- English proof (translation)
Apply `(hs _ _ V).1` to reduce the goal to its premises. Use `loc_bind ((hp q V).2.2.2 hq u) (fun W g ha => ?_)` and prove the remaining obligations. Take `⟨a, ha⟩` from `ha`. Use `loc_mono ((hp q W).2.2.2 (unit_q q g hq) (Units.map g.appTop.hom.toMonoidHom v)) (fun W' k hb => ?_)` and prove the remaining obligations. Take `⟨b, hb⟩` from `hb`.

Establish `ha' : (Units.map k.appTop.hom.toMonoidHom a) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u`. Rewrite using `[← map_pow, ha, umap_comp]`. Establish `hb' : b ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom v` using `by rw [hb, umap_comp]`. Rewrite using `[h₁ W' (k ≫ g) _ b ha' hb', h₂ W' (k ≫ g) _ b ha' hb']`.
-/
theorem KP_uniq (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) {u v : (Γ(V, ⊤))ˣ} {Z₁ Z₂ : Sec ((res _ (tw q 1)).X 0) V}
    (h₁ : KP q u v Z₁) (h₂ : KP q u v Z₂) : Z₁ = Z₂ := by
  apply (hs _ _ V).1
  refine loc_bind ((hp q V).2.2.2 hq u) (fun W g ha => ?_)
  obtain ⟨a, ha⟩ := ha
  refine loc_mono ((hp q W).2.2.2 (unit_q q g hq) (Units.map g.appTop.hom.toMonoidHom v)) (fun W' k hb => ?_)
  obtain ⟨b, hb⟩ := hb
  have ha' : (Units.map k.appTop.hom.toMonoidHom a) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
    rw [← map_pow, ha, umap_comp]
  have hb' : b ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom v := by rw [hb, umap_comp]
  rw [h₁ W' (k ≫ g) _ b ha' hb', h₂ W' (k ≫ g) _ b ha' hb']

/- English proof (translation)
Set `S : Sieve V` to `{ arrows := fun W g => (∃ a : (Γ(W, ⊤))ˣ, a ^ q = Units.map g.appTop.hom.toMonoidHom u) ∧ ∃ b : (Γ(W, ⊤))ˣ, b ^ q = Units.map g.appTop.hom.toMonoidHom v downward_closed := by`. Introduce and unpack `W W' g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ k`. Conclude with `⟨⟨Units.map k.appTop.hom.toMonoidHom a, by rw [← map_pow, ha, umap_comp]⟩, ⟨Units.map k.appTop.hom.toMonoidHom b, by rw [← map_pow, hb, umap_comp]⟩⟩ }`. Establish `hS : S ∈ Scheme.etaleTopology V`. Take `⟨S₁, h₁, P₁⟩` from `(hp q V).2.2.2 hq u`.

Take `⟨S₂, h₂, P₂⟩` from `(hp q V).2.2.2 hq v`. Use `Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering h₁ h₂)` and prove the remaining obligations. Introduce `W g hg`. Conclude with `⟨P₁ W g hg.1, P₂ W g hg.2⟩`. Set `sfun : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → Sec ((res _ (tw q 1)).X 0) W` to `fun W g hg => D q W (Classical.choose (And.left hg)) (Classical.choose (And.right hg))`.

Take `⟨Z, hZ⟩` from `(hs _ _ V).2 S hS sfun (by`. Introduce `W W' g k hg`. Rewrite using `[D_res q hk k (unit_q q g hq)]`. Use `D_change2 q hk hp hs (unit_q q (k ≫ g) hq) _ _ _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, hg.1.choose_spec, ← umap_comp, (S.downward_closed hg k).1.choose_spec]`.

Rewrite using `[← map_pow, hg.2.choose_spec, ← umap_comp, (S.downward_closed hg k).2.choose_spec])`. Use `⟨Z, fun W g a b ha hb => ?_⟩` and prove the remaining obligations. Establish `hg : S.arrows g` using `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`. Rewrite using `[hZ W g hg]`. Conclude with `D_change2 q hk hp hs (unit_q q g hq) _ _ _ _ (by rw [hg.1.choose_spec, ha]) (by rw [hg.2.choose_spec, hb])`.
-/
theorem KP_exists (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (u v : (Γ(V, ⊤))ˣ) : ∃ Z, KP q u v Z := by
  classical
  let S : Sieve V :=
    { arrows := fun W g => (∃ a : (Γ(W, ⊤))ˣ, a ^ q = Units.map g.appTop.hom.toMonoidHom u) ∧
        ∃ b : (Γ(W, ⊤))ˣ, b ^ q = Units.map g.appTop.hom.toMonoidHom v
      downward_closed := by
        rintro W W' g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ k
        exact ⟨⟨Units.map k.appTop.hom.toMonoidHom a, by rw [← map_pow, ha, umap_comp]⟩,
          ⟨Units.map k.appTop.hom.toMonoidHom b, by rw [← map_pow, hb, umap_comp]⟩⟩ }
  have hS : S ∈ Scheme.etaleTopology V := by
    obtain ⟨S₁, h₁, P₁⟩ := (hp q V).2.2.2 hq u
    obtain ⟨S₂, h₂, P₂⟩ := (hp q V).2.2.2 hq v
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering h₁ h₂)
    intro W g hg
    exact ⟨P₁ W g hg.1, P₂ W g hg.2⟩
  let sfun : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → Sec ((res _ (tw q 1)).X 0) W :=
    fun W g hg => D q W (Classical.choose (And.left hg)) (Classical.choose (And.right hg))
  obtain ⟨Z, hZ⟩ := (hs _ _ V).2 S hS sfun (by
    intro W W' g k hg
    rw [D_res q hk k (unit_q q g hq)]
    refine D_change2 q hk hp hs (unit_q q (k ≫ g) hq) _ _ _ _ ?_ ?_
    · rw [← map_pow, hg.1.choose_spec, ← umap_comp, (S.downward_closed hg k).1.choose_spec]
    · rw [← map_pow, hg.2.choose_spec, ← umap_comp, (S.downward_closed hg k).2.choose_spec])
  refine ⟨Z, fun W g a b ha hb => ?_⟩
  have hg : S.arrows g := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [hZ W g hg]
  exact D_change2 q hk hp hs (unit_q q g hq) _ _ _ _ (by rw [hg.1.choose_spec, ha]) (by rw [hg.2.choose_spec, hb])

/- English proof (translation)
The claim follows from `map_add _ _ _`.
-/
theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s + t) = Sec.res g s + Sec.res g t := map_add _ _ _

noncomputable def yv {X : Scheme.{0}} (Y : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res (ZMod q) (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec ((res (ZMod q) (tw q 1)).X s) U
  | 0, s, h, U, x => by
      obtain rfl : s = 0 := by simpa using h.symm
      exact Y U x
  | _ + 1, _, _, _, _ => 0

end LateralTheory.EtaleFoundations.KMC

namespace LateralTheory.EtaleFoundations
open KMC

/- English proof (translation)
Introduce `q _ X u v hq γu γv ku kv`. Establish `hk` using `hkT q`. Establish `hY : ∀ (U : Scheme.{0}) (x : U ⟶ X), ∃ Z, KP q (Units.map x.appTop.hom.toMonoidHom u) (Units.map x.appTop.hom.toMonoidHom v) Z` using `fun U x => KP_exists q hk hp hs (unit_q q x hq) _ _`. Use `choose Y hYP using hY`. Establish `hYnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (Y U x) = Y V (g ≫ x)`.

Introduce `V U g x`. Use `KP_uniq q hp hs (unit_q q (g ≫ x) hq) ?_ (hYP V (g ≫ x))` and prove the remaining obligations. Use `KP_res q g (hYP U x)` as an intermediate fact. Rewrite `this` using `[← umap_comp, ← umap_comp]`. Then use the resulting hypothesis. Take `⟨y, hy⟩` from `hmk (ZMod q) (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) (yv q Y) (by`.

Introduce `p s h V U g x`. Consider the cases of `p with`. Consider the case `zero`. Take `rfl : s = 0` from `by simpa using h.symm`. Conclude with `hYnat V U g x`.

Consider the case `succ p => show Sec.res g 0 = 0`. Conclude with `map_zero _)`. Set `β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1` to `Cocycle.mk (δ 0 1 y) 2 (by norm_num) (δ_δ 0 1 2 y)`. Establish `e : (γu + γv + β).1 = γu.1 + γv.1 + δ 0 1 y` using `rfl`. Establish `hadd1 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X), ev (α + β') 1 0 (by simp) U x = ev α 1 0 (by simp) U x + ev β' 1 0 (by simp) U x` using `fun α β' U x => ((hb (ZMod q)).1 α β' 1 0 _ U x).1`.

Establish `hadd0 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X), ev (α + β') 0 1 (by simp) U x = ev α 0 1 (by simp) U x + ev β' 0 1 (by simp) U x` using `fun α β' U x => ((hb (ZMod q)).1 α β' 0 1 _ U x).1`. Establish `hδ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (δ 0 1 y) 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (Y U x)` using `fun U x => ((hd (ZMod q) (n := 0) (m := 1) rfl y U).1 x).trans (congrArg _ (hy 0 0 _ U x))`. Use `⟨γu + γv + β, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `U x`. Rewrite using `[e]`.

Rewrite using `[hadd1, hadd1]`. Rewrite using `[ku.1 U x, kv.1 U x, zero_add, zero_add]`. Use `((hd (ZMod q) (n := 0) (m := 1) rfl y U).2 0 (-1) 0 (by simp) (by simp) x).trans ?_` and prove the remaining obligations. Establish `hy1 : ev y (0 + 1) (-1) (by simp) U x = 0` using `hy 1 (-1) _ U x`. Establish `hface : ∀ i, ev y 0 0 (by simp) U (Sx.face (E` using `sch.obj X) (p := 0) x i) = Y U x := fun i => hy 0 0 _ U _`.

Rewrite using `[hy1]`. Simplify using `only [hface]`. Simplify using `[Fin.sum_univ_two, Sec.map]`. Introduce `U x w hw`. Rewrite using `[e]`.

Rewrite using `[hadd0, hadd0, hδ0]`. Apply `(hs _ _ U).1` to reduce the goal to its premises. Use `loc_mono ((hp q U).2.2.2 (unit_q q x hq) (Units.map x.appTop.hom.toMonoidHom u)) (fun W k ha => ?_)` and prove the remaining obligations. Take `⟨a, ha⟩` from `ha`. Use `set K := Units.map k.appTop.hom.toMonoidHom w with hK`.

Establish `hbq : (K * a⁻¹) ^ q = Units.map k.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom v)`. Rewrite using `[mul_pow, inv_pow, hK, ← map_pow, hw, ha, map_mul, map_mul, mul_comm (Units.map _ (Units.map _ u)), mul_inv_cancel_right]`. Establish `hab : a * (K * a⁻¹) = K` using `by rw [mul_comm K, mul_inv_cancel_left]`. Establish `eu : Sec.res k (ev γu.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W a)` using `((hb (ZMod q)).2.1 γu.1 0 1 (by simp) W U k x).trans (ku.2 W (k ≫ x) a (by rw [ha, umap_comp]))`. Establish `ev' : Sec.res k (ev γv.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W (K * a⁻¹))` using `((hb (ZMod q)).2.1 γv.1 0 1 (by simp) W U k x).trans (kv.2 W (k ≫ x) _ (by rw [hbq, umap_comp]))`.

Rewrite using `[res_add, res_add, eu, ev', res_map, res_map, hYP U x W k a (K * a⁻¹) ha hbq, hk.1 W U k w (unit_q q x hq)]`. Rewrite using `[← hK]`. Unfold `D`. Rewrite using `[hab]`. Simplify using `only [Sec.map, map_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[CohomologyClass.mk_add, CohomologyClass.mk_add, (CohomologyClass.mk_eq_zero_iff β).2 ((mem_coboundaries_iff β 0 (by norm_num)).2 ⟨y, rfl⟩), add_zero]`.
-/
theorem kum_mul_coc_of (hkT : EtaleKummerTriangleExists) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue)
    (hmk : EtaleCochainExistsOfNaturalEvaluation) (hd : EtaleCochainEvaluationCoboundaryFormula) (hb : EtaleCochainEvaluationLinear) : kum_mul_coc := by
  intro q _ X u v hq γu γv ku kv
  have hk := hkT q
  have hY : ∀ (U : Scheme.{0}) (x : U ⟶ X), ∃ Z, KP q (Units.map x.appTop.hom.toMonoidHom u)
      (Units.map x.appTop.hom.toMonoidHom v) Z :=
    fun U x => KP_exists q hk hp hs (unit_q q x hq) _ _
  choose Y hYP using hY
  have hYnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (Y U x) = Y V (g ≫ x) := by
    intro V U g x
    refine KP_uniq q hp hs (unit_q q (g ≫ x) hq) ?_ (hYP V (g ≫ x))
    have := KP_res q g (hYP U x)
    rwa [← umap_comp, ← umap_comp] at this
  obtain ⟨y, hy⟩ := hmk (ZMod q) (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) (yv q Y) (by
    intro p s h V U g x
    cases p with
    | zero =>
      obtain rfl : s = 0 := by simpa using h.symm
      exact hYnat V U g x
    | succ p =>
      show Sec.res g 0 = 0
      exact map_zero _)
  let β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1 :=
    Cocycle.mk (δ 0 1 y) 2 (by norm_num) (δ_δ 0 1 2 y)
  have e : (γu + γv + β).1 = γu.1 + γv.1 + δ 0 1 y := rfl
  have hadd1 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 1 0 (by simp) U x = ev α 1 0 (by simp) U x + ev β' 1 0 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 1 0 _ U x).1
  have hadd0 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 0 1 (by simp) U x = ev α 0 1 (by simp) U x + ev β' 0 1 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 0 1 _ U x).1
  have hδ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (δ 0 1 y) 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (Y U x) :=
    fun U x => ((hd (ZMod q) (n := 0) (m := 1) rfl y U).1 x).trans (congrArg _ (hy 0 0 _ U x))
  refine ⟨γu + γv + β, ⟨?_, ?_⟩, ?_⟩
  · intro U x
    rw [e]
    rw [hadd1, hadd1]
    rw [ku.1 U x, kv.1 U x, zero_add, zero_add]
    refine ((hd (ZMod q) (n := 0) (m := 1) rfl y U).2 0 (-1) 0 (by simp) (by simp) x).trans ?_
    have hy1 : ev y (0 + 1) (-1) (by simp) U x = 0 := hy 1 (-1) _ U x
    have hface : ∀ i, ev y 0 0 (by simp) U (Sx.face (E := sch.obj X) (p := 0) x i) = Y U x := fun i => hy 0 0 _ U _
    rw [hy1]
    simp only [hface]
    simp [Fin.sum_univ_two, Sec.map]
  · intro U x w hw
    rw [e]
    rw [hadd0, hadd0, hδ0]
    apply (hs _ _ U).1
    refine loc_mono ((hp q U).2.2.2 (unit_q q x hq) (Units.map x.appTop.hom.toMonoidHom u)) (fun W k ha => ?_)
    obtain ⟨a, ha⟩ := ha
    set K := Units.map k.appTop.hom.toMonoidHom w with hK
    have hbq : (K * a⁻¹) ^ q = Units.map k.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom v) := by
      rw [mul_pow, inv_pow, hK, ← map_pow, hw, ha, map_mul, map_mul, mul_comm (Units.map _ (Units.map _ u)),
        mul_inv_cancel_right]
    have hab : a * (K * a⁻¹) = K := by rw [mul_comm K, mul_inv_cancel_left]
    have eu : Sec.res k (ev γu.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W a) :=
      ((hb (ZMod q)).2.1 γu.1 0 1 (by simp) W U k x).trans (ku.2 W (k ≫ x) a (by rw [ha, umap_comp]))
    have ev' : Sec.res k (ev γv.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W (K * a⁻¹)) :=
      ((hb (ZMod q)).2.1 γv.1 0 1 (by simp) W U k x).trans (kv.2 W (k ≫ x) _ (by rw [hbq, umap_comp]))
    rw [res_add, res_add, eu, ev', res_map, res_map, hYP U x W k a (K * a⁻¹) ha hbq, hk.1 W U k w (unit_q q x hq)]
    rw [← hK]
    unfold D
    rw [hab]
    simp only [Sec.map, map_sub]
    abel
  · rw [CohomologyClass.mk_add, CohomologyClass.mk_add,
      (CohomologyClass.mk_eq_zero_iff β).2 ((mem_coboundaries_iff β 0 (by norm_num)).2 ⟨y, rfl⟩), add_zero]

end LateralTheory.EtaleFoundations
