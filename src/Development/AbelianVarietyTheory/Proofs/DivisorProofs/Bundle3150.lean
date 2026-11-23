module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevForget

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def forgetMap {b : Base D R} {N' : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'}
    {o : Obj b N' s} {f : S' ⟶ S} (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) :
    ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

end GlobalTheory.UPel.HT.EtLev.LevForget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem isSeparated_model_str {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have : IsSeparated (PSpace.str R n) := by
    unfold PSpace.str
    infer_instance
  rw [← e]
  infer_instance

theorem exists_heckeMap_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hg hgk hck M M'
  have hp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (Nat.coprime_zero_left p |>.1 hk) hp.ne_one
    · exact h
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := _root_.GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude p D g c k hc hk hg hgk hck
  have h3' : ∀ x y, D.EF (g' x) (g' y) = ((k ^ 2 / c : ℕ) : ℤ) * D.EF x y := by
    intro x y
    rw [h3 x y]
    push_cast
    rfl
  have c1 : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have c2 : (N * k * k).Coprime p := Nat.Coprime.mul_left c1 hk
  have c3 : (N * k * k * k).Coprime p := Nat.Coprime.mul_left c2 hk
  have l1 : 3 ≤ N * k := hN.trans (Nat.le_mul_of_pos_right _ hk0)
  have l2 : 3 ≤ N * k * k := l1.trans (Nat.le_mul_of_pos_right _ hk0)
  have l3 : 3 ≤ N * k * k * k := l2.trans (Nat.le_mul_of_pos_right _ hk0)
  obtain ⟨M₂⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k) l2 c2
  obtain ⟨M₃⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k * k) l3 c3
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k N hc hk hN hNp hg hgk hck M M'
  obtain ⟨π₁, hπ₁⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g' (k ^ 2 / c) k (N * k) h5 hk l1 c1 h3' h4 h6 M' M₂
  obtain ⟨π₂, hπ₂⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k (N * k * k) hc hk l2 c2 hg hgk hck M₂ M₃
  have e : π ≫ M.s = M'.s := hπ.1
  have e₁ : π₁ ≫ M'.s = M₂.s := hπ₁.1
  have e₂ : π₂ ≫ M₂.s = M₃.s := hπ₂.1
  have f1 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g g' c (k ^ 2 / c) k N hk hN hNp h1 h2 h7 c2 M.toRepFam M'.toRepFam
    M₂.toRepFam π π₁ hπ hπ₁
  have f2 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g' g (k ^ 2 / c) c k (N * k) hk l1 c1 h2 h1 (by rw [mul_comm, h7]) c3
    M'.toRepFam M₂.toRepFam M₃.toRepFam π₁ π₂ hπ₁ hπ₂
  obtain ⟨a1, a2, a3⟩ := _root_.GlobalTheory.UPel.HT.forget_map_finite_etale_surjective p D R b N (N * k * k) _ c2 hN M M₂ (π₁ ≫ π)
    (by rw [Category.assoc, e, e₁]) f1
  obtain ⟨-, -, b3⟩ := _root_.GlobalTheory.UPel.HT.forget_map_finite_etale_surjective p D R b (N * k) (N * k * k * k) _ c3 l1 M' M₃ (π₂ ≫ π₁)
    (by rw [Category.assoc, e₁, e₂]) f2
  have s1 : Surjective π₁ := Surjective.of_comp π₂ π₁
  have t1 : Etale π₁ := GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension _ _ _ _ π₁ π M₂.s M'.s _ e₁ M₂.smooth M'.smooth a2
  have hs : IsSeparated π := by
    have : IsSeparated (π ≫ M.s) := e ▸ isSeparated_model_str M'
    exact IsSeparated.of_comp π M.s
  have hl : LocallyOfFiniteType π := by
    have := M'.smooth
    have : Smooth M'.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M'.s
    have : LocallyOfFiniteType (π ≫ M.s) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp π M.s
  obtain ⟨r1, r2⟩ := GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' _ _ _ π₁ π t1 s1 a2 a1 hs hl
  exact ⟨π, hπ, r2, r1, Surjective.of_comp π₁ π⟩

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonempty
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

def GBase.toBaseAt (gb : GBase D.toG R) : Base D R where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst this
      exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h := ((IsUnit.mk0 _ hp).map (algebraMap ℚ R)).map β
    simp at h

theorem fullTate (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R} (o : Obj gb.toBaseAt N s)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k) (h : x ≫ s = spMap β) :
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  haveI : CharZero k := by
    letI : Algebra ℚ k := (β.comp (algebraMap ℚ R)).toAlgebra
    exact algebraRat.charZero k
  exact GlobalTheory.T.exists_tate_module_iso p D R gb.toBaseAt N h3 hN S s o k x β h

theorem kerPrimeTo {gb : GBase D.toG R} {N : ℕ} (h3 : 3 ≤ N) {s : S ⟶ Sp R} (o : GObj gb N s) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 :=
  GlobalTheory.T.torsion_of_generating_section p D R gb N h3 S s o

def GTateIso.toPrimeTo {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n h _ := I.ζ_prim n h
  ζ_pow n m h h' _ := I.ζ_pow n m h h'
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n h _ := I.ker n h
  onto n h _ := I.onto n h
  tower n m h h' _ := I.tower n m h h'
  isom n h _ := I.isom n h

def GBase.ofObjAt (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R}
    (o : Obj gb.toBaseAt N s) : GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fullTate gb h3 hN o

def GObj.toObjAt {gb : GBase D.toG R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) (h3 : 3 ≤ N) :
    Obj gb.toBaseAt N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := kerPrimeTo h3 o
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    exact ⟨I.toPrimeTo, hI⟩

def GBase.genModelOf (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) (M : Model gb.toBaseAt N) :
    GenModel gb N where
  X := M.X
  s := M.s
  univ := gb.ofObjAt h3 hN M.univ
  rep S s' o := by
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := M.rep S s' (o.toObjAt h3)
    refine ⟨f, ⟨hf, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨n⟩⟩
    exact hu g ⟨hg, ⟨⟨n.φ, n.φ₂, n.cart, n.sq, n.act, n.pol, n.eta⟩⟩⟩

theorem genModel_nonempty (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ) (h3 : 3 ≤ N) (hN : N.Coprime p) :
    Nonempty (GenModel gb N) := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R' gb.toBaseAt N h3 hN
  exact ⟨gb.genModelOf h3 hN M⟩

end GlobalTheory.UPel.HT.Gen
end
end

