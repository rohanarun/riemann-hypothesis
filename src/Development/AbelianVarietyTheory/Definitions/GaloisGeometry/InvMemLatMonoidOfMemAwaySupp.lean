module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.EqOneOfHeckeEigNeBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMonHomIdPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0001
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.HeckeCorr
open scoped TensorProduct

section Side

variable {Γ : Type} [Group Γ]

theorem mem_heckeLevel_inv {K : Subgroup Γ} {h u : Γ} : u ∈ heckeLevel K h⁻¹ ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := by
  refine ⟨fun hu => ⟨heckeLevel_le K h⁻¹ hu, by simpa using conj_mem_of_mem_heckeLevel hu⟩, fun hu => ⟨hu.1, ?_⟩⟩
  exact ⟨h * u * h⁻¹, hu.2, by simp [MulAut.conj_apply, _root_.mul_assoc]⟩

theorem heckeLevel_inv_of_comm (K : Subgroup Γ) {h : Γ} (hc : ∀ u, h * u = u * h) : heckeLevel K h⁻¹ = K := by
  ext u
  rw [mem_heckeLevel_inv, hc u, mul_inv_cancel_right, and_self]


end Side

section Corr

variable {G₀ : GDatum} {gb : GBase G₀ ℂ}

structure Corr {N N' : ℕ} (X : GenModel gb N) (X' : GenModel gb N') where

  q1 : X'.X ⟶ X.X

  q2 : X'.X ⟶ X.X
  firstProjection_structure : q1 ≫ X.s = X'.s
  secondProjection_structure : q2 ≫ X.s = X'.s

  φ1 : X'.univ.A.left ⟶ X.univ.A.left

  φ2 : X'.univ.A.left ⟶ X.univ.A.left
  φ1_w : φ1 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q1
  φ2_w : φ2 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q2

namespace Corr

variable {N N' : ℕ} {X : GenModel gb N} {X' : GenModel gb N'} (C : Corr X X') (k : ℕ)

def c1 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q1 C.φ1 C.φ1_w k

def c2 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q2 C.φ2 C.φ2_w k


theorem firstLeg_overComplex : C.c1 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c1, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.firstProjection_structure]

theorem secondLeg_overComplex : C.c2 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c2, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.secondProjection_structure]


def op [IsFinite (C.c1 k)] [Etale (C.c1 k)] (a b : ℕ) : hodgeH (zs X k) a b →ₗ[ℂ] hodgeH (zs X k) a b :=
  corrOp (C.c1 k) (C.c2 k) (C.firstLeg_overComplex k) (C.secondLeg_overComplex k) a b



def mulBy (X : GenModel gb N) (c : ℕ) : Corr X X where
  q1 := 𝟙 _
  q2 := 𝟙 _
  firstProjection_structure := Category.id_comp _
  secondProjection_structure := Category.id_comp _
  φ1 := 𝟙 _
  φ2 := (𝟙 X.univ.A ^ c).left
  φ1_w := by simp
  φ2_w := by simp

theorem mulBy_secondLeg_projection (X : GenModel gb N) (c : ℕ) (i : Fin k) :
    (mulBy X c).c2 k ≫ (GlobalTheory.KS.pr X.univ.A i).left = (GlobalTheory.KS.pr X.univ.A i ^ c).left := by
  rw [c2, GlobalTheory.KS.PowPB.powMap_pr]
  show _ ≫ (𝟙 X.univ.A ^ c).left = _
  rw [← Over.comp_left, GlobalTheory.DrinLev.HT.MulModel.comp_pow', Category.comp_id]

def IsForget {k' : ℕ} {X' : GenModel gb (N * k')} (C : Corr X X') : Prop :=
  ∃ (hN : 0 < N) (hk : 0 < k') (m : GObjMap (X'.univ.forgetMul hN hk) X.univ C.q1), C.φ1 = m.φ

end Corr

theorem powMap_id_eq {S : Scheme.{0}} (A : Over S) (h : 𝟙 A.left ≫ A.hom = A.hom ≫ 𝟙 S) (k : ℕ) :
    GlobalTheory.KS.powMap (𝟙 S) (𝟙 A.left) h k = 𝟙 _ := by
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [GlobalTheory.KS.PowPB.powMap_w]; simp
  · intro i; rw [GlobalTheory.KS.PowPB.powMap_pr]; simp

theorem corrOp_of_eq_id {Y : Scheme.{0}} {s : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Y} [IsFinite c1] [Etale c1] (e : c1 = 𝟙 Y)
    (h1 : c1 ≫ s = s) (h2 : c2 ≫ s = s) (a b : ℕ) : corrOp c1 c2 h1 h2 a b = hodgePull h2 a b := by
  subst e
  exact LinearMap.ext fun x => hodgeTrace_id s a b _

end Corr

section Relevel

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G₀ R} {N M : ℕ}

def relevelObj (e : N = M) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj gb N s) : GObj gb M s :=
  { o with eta_ker := e ▸ o.eta_ker, geom := e ▸ o.geom }

def relevelModel (e : N = M) (X : GenModel gb N) : GenModel gb M where
  X := X.X
  s := X.s
  univ := relevelObj e X.univ
  rep S s' o := by subst e; exact X.rep S s' o

end Relevel

section Wit

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

abbrev GTIsoAt {gb : GBase G₀ R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k]
    (t : Sp k ⟶ S) : Type :=
  GTateIso G₀ k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def GInducesAt {gb : GBase G₀ R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k]
    (t : Sp k ⟶ S) (I : GTIsoAt o t) : Prop :=
  ∀ y, toUnit _ ≫ o.eta y = I.ev N y

theorem gTateIso_ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : G₀.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G₀ k Q act e) (n c : ℕ) (x : G₀.La) : I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG R}

def GActsAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : GObj gb N' s} {o'' : GObj gb N s} {k : Type} [Field k]
    {t : Sp k ⟶ S} (I' : GTIsoAt o' t) (I'' : GTIsoAt o'' t) (ψ : o'.A ⟶ o''.A) (m : ℤ) (h : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, m • L.actG h (inAf D x) = inAf D y + n • v

def IsGIsogWit (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s)
    (ψ : o'.A ⟶ o''.A) (ψ' : o''.A ⟶ o'.A) (m d : ℕ) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
    ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ m.Coprime p ∧ d.Coprime p ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : R →+* k), t ≫ s = spMap β →
      ∃ (I' : GTIsoAt o' t) (I'' : GTIsoAt o'' t), GInducesAt o' t I' ∧ GInducesAt o'' t I'' ∧
        GActsAt L I' I'' ψ m h

def IsGHeckeWit (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) (q : X'.X ⟶ X.X)
    (o'' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ X'.univ.A) (m d : ℕ)
    (_φ : GObjMap o'' X.univ q) : Prop :=
  q ≫ X.s = X'.s ∧ IsGIsogWit L h X'.univ o'' ψ ψ' m d

def latMonoid : Submonoid G.GAf where
  carrier := {h | ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D}
  one_mem' := fun v hv => by rw [map_one]; exact hv
  mul_mem' := fun {a b} ha hb v hv => by rw [map_mul, Module.End.mul_apply]; exact ha _ (hb v hv)

theorem smul_mem_laHat {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a', x, ha', rfl⟩ := hu
    refine AddSubgroup.subset_closure ⟨a * a', x, fun w => ?_, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
    rw [map_mul]
    exact mul_mem (ha w) (ha' w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => rw [smul_add]; exact add_mem hu hu'
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

def scalarAf (G : HTGroup p) (a : (AfP p)ˣ) : G.GAf :=
  ⟨(Units.map (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)).toMonoidHom a, a * a), by
    show algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a * (starT G.star (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((a : AfP p) * a)
    have e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a = (a : AfP p) ⊗ₜ[ℚ] (1 : G.C) := rfl
    rw [map_mul, e, starT_tmul, map_one, MulOpposite.unop_one]⟩

theorem actG_scalarAf (a : (AfP p)ˣ) (v : AfP p ⊗[ℚ] VQ D) : L.actG (scalarAf G a) v = (a : AfP p) • v := by
  show actOn L.rep (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a) v = _
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

theorem scalarAf_comm (a : (AfP p)ˣ) (u : G.GAf) : scalarAf G a * u = u * scalarAf G a :=
  Subtype.ext (Prod.ext (Units.ext (Algebra.commutes (a : AfP p) _)) (mul_comm _ _))

def natUnit (p : ℕ) (c : ℕ) (hc : c ≠ 0) : (AfP p)ˣ :=
  Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 (c : ℚ) (Nat.cast_ne_zero.2 hc))

theorem actG_natScalar (c : ℕ) (hc : c ≠ 0) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG (scalarAf G (natUnit p c hc)) v = c • v := by
  rw [actG_scalarAf]
  show algebraMap ℚ (AfP p) (c : ℚ) • v = _
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem isGIsogWit_mul {S : Scheme.{0}} {s : S ⟶ Sp R} {N M : ℕ} (e : N = M) (o : GObj gb N s) {h : G.GAf} {m c : ℕ}
    (hm : m.Coprime p) (hc : c.Coprime p) (hh : ∀ v, (m : ℤ) • L.actG h v = c • v) :
    IsGIsogWit L h (relevelObj e o) o (𝟙 o.A ^ c) (𝟙 o.A ^ c) m (c * c) := by
  subst e
  show IsGIsogWit L h o o (𝟙 o.A ^ c) (𝟙 o.A ^ c) m (c * c)
  haveI := GlobalTheory.DrinLev.HT.MulModel.isMonHom_id_pow o.A c
  refine ⟨inferInstance, inferInstance, fun a => ?_, fun a => ?_, ?_, ?_, hm, Nat.Coprime.mul_left hc hc,
    fun k _ _ t β ht => ?_⟩
  · haveI := o.act.hom a
    rw [MonObj.comp_pow, GlobalTheory.DrinLev.HT.MulModel.pow_comp', Category.comp_id, Category.id_comp]
  · haveI := o.act.hom a
    rw [MonObj.comp_pow, GlobalTheory.DrinLev.HT.MulModel.pow_comp', Category.comp_id, Category.id_comp]
  · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  obtain ⟨I, hI⟩ := o.geom k t β ht
  refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
  have e1 : (m : ℤ) • L.actG h (inAf D x) = ((1 : ℕ) : ℤ) • L.actG 1 (inAf D (c • x)) := by
    rw [hh]
    simp only [map_one, Module.End.one_apply, Nat.cast_one, one_smul]
    exact (map_nsmul (ForgetHecke.inAfHom D) c x).symm
  show I.ev n x ≫ 𝟙 o.A ^ c = I.ev n y ↔ _
  rw [e1, ForgetHecke.acts_one_iff L n hn hnp (c • x) y, MonObj.comp_pow, Category.comp_id]
  refine Iff.trans ?_ (I.ker n hn (c • x - y))
  have hx : I.ev n x ^ c = I.ev n (c • x - y) * I.ev n y :=
    (gTateIso_ev_nsmul I n c x).symm.trans
      ((congrArg (I.ev n) (sub_add_cancel (c • x) y).symm).trans (I.add n (c • x - y) y))
  rw [hx]
  exact mul_eq_right

end Wit

section Op

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

def hkIndex (N N' : ℕ) (h : G.GAf) : ℕ := (L.KN N').relIndex (heckeLevel (L.KN N) h⁻¹)

theorem relIndex_KN_ne_zero {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') : (L.KN N').relIndex (L.KN N) ≠ 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  obtain ⟨K', hK'⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N' hN'
  haveI : CompactSpace (L.KN N) := isCompact_iff_compactSpace.1 (hK ▸ K.compact)
  have ho : IsOpen ((L.KN N').subgroupOf (L.KN N) : Set (L.KN N)) :=
    (show IsOpen (L.KN N' : Set G.GAf) from hK' ▸ K'.K.isOpen).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

def IsAdelicHecke (h : G.GAf) {k' : ℕ} {X : GenModel gb N} {X' : GenModel gb (N * k')} (C : Corr X X') : Prop :=
  (N * k').Coprime p ∧ L.KN (N * k') ≤ heckeLevel (L.KN N) h⁻¹ ∧ C.IsForget ∧
    ∃ (o'' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o''.A) (ψ' : o''.A ⟶ X'.univ.A) (d : ℕ) (φ : GObjMap o'' X.univ C.q2),
      IsGHeckeWit L h X' X C.q2 o'' ψ ψ' 1 d φ ∧ C.φ2 = ψ.left ≫ φ.φ

theorem KN_mul_le (N k' : ℕ) : L.KN (N * k') ≤ L.KN N := by
  have key : ∀ g, L.CongOne (N * k') g → L.CongOne N g := fun g hg v hv => by
    obtain ⟨w, hw, e⟩ := hg v hv
    exact ⟨k' • w, nsmul_mem hw k', by rw [e, mul_smul]⟩
  exact fun g hg => ⟨key _ hg.1, key _ hg.2⟩

def IsHeckeOpZ (X : GenModel gb N) (k : ℕ) (h : G.GAf) (a b : ℕ) (T : Module.End ℂ (hodgeH (zs X k) a b)) : Prop :=
  ∃ (k' : ℕ) (X' : GenModel gb (N * k')) (C : Corr X X') (_ : IsFinite (C.c1 k)) (_ : Etale (C.c1 k)),
    IsAdelicHecke L h C ∧ T = ((hkIndex L N (N * k') h : ℂ))⁻¹ • C.op k a b

def mulPull {G₀ : GDatum} {gb : GBase G₀ ℂ} (X : GenModel gb N) (k c a b : ℕ) : Module.End ℂ (hodgeH (zs X k) a b) :=
  hodgePull ((Corr.mulBy X c).secondLeg_overComplex k) a b

theorem mulPull_one {G₀ : GDatum} {gb : GBase G₀ ℂ} (X : GenModel gb N) (k a b : ℕ) : mulPull X k 1 a b = 1 := by
  have e : (Corr.mulBy X 1).c2 k = 𝟙 _ := by
    apply GlobalTheory.KS.PowPB.pow_left_hom_ext
    · rw [Corr.c2, GlobalTheory.KS.PowPB.powMap_w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
    · intro i; rw [Corr.mulBy_secondLeg_projection, pow_one, Category.id_comp]
  have key : ∀ (f : Z X k ⟶ Z X k) (hf : f ≫ zs X k = zs X k), f = 𝟙 _ → hodgePull hf a b = 1 := by
    rintro _ hf rfl
    exact LinearMap.ext fun x => hodgePull_id _ a b x
  exact key _ _ e

theorem isHeckeOpZ_of_mul (hN : N.Coprime p) (X : GenModel gb N) (k : ℕ) {h : G.GAf} {c : ℕ} (hc : c.Coprime p)
    (hcomm : ∀ u, h * u = u * h) (hh : ∀ v, L.actG h v = c • v) (a b : ℕ) :
    IsHeckeOpZ L X k h a b (mulPull X k c a b) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h0 => (Fact.out : p.Prime).ne_one (by simpa [h0] using hN)
  let X' : GenModel gb (N * 1) := relevelModel (Nat.mul_one N).symm X
  let C₀ := Corr.mulBy X c
  let C : Corr X X' := ⟨C₀.q1, C₀.q2, C₀.firstProjection_structure, C₀.secondProjection_structure, C₀.φ1, C₀.φ2, C₀.φ1_w, C₀.φ2_w⟩
  have e1 : C.c1 k = 𝟙 (Z X k) := powMap_id_eq X.univ.A _ k
  have hf : IsFinite (C.c1 k) := by rw [e1]; exact inferInstanceAs (IsFinite (𝟙 (Z X k)))
  have he : Etale (C.c1 k) := by rw [e1]; exact inferInstanceAs (Etale (𝟙 (Z X k)))
  let m₀ : GObjMap X.univ X.univ (𝟙 X.X) :=
    { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id X.univ.A, sq := ⟨by simp, by simp⟩,
      act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id X.univ.isLB, eta := fun y => by simp }
  have hlev : heckeLevel (L.KN N) h⁻¹ = L.KN (N * 1) := by rw [heckeLevel_inv_of_comm _ hcomm, Nat.mul_one]
  refine ⟨1, X', C, hf, he, ⟨by rwa [Nat.mul_one], hlev.ge, ⟨hN0, one_pos,
    ⟨m₀.φ, m₀.φ₂, m₀.cart, m₀.sq, m₀.act, m₀.pol, fun y => ?_⟩, rfl⟩, X.univ, 𝟙 X.univ.A ^ c, 𝟙 X.univ.A ^ c, c * c, m₀,
    ⟨Category.id_comp _, isGIsogWit_mul L (Nat.mul_one N).symm X.univ (Nat.coprime_one_left p) hc fun v => ?_⟩,
    (Category.comp_id _).symm⟩, ?_⟩
  · show (X.univ.eta (1 • y)).left ≫ _ = _
    rw [one_nsmul]
    exact m₀.eta y
  · rw [Nat.cast_one, one_smul, hh]
  · rw [hkIndex, hlev, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    exact (@corrOp_of_eq_id _ (zs X k) (C.c1 k) (C.c2 k) hf he e1 (C.firstLeg_overComplex k) (C.secondLeg_overComplex k) a b).symm

theorem isHeckeOpZ_one (hN : N.Coprime p) (X : GenModel gb N) (k a b : ℕ) : IsHeckeOpZ L X k 1 a b 1 := by
  rw [← mulPull_one X k a b]
  exact isHeckeOpZ_of_mul L hN X k (Nat.coprime_one_left p) (fun u => by simp) (fun v => by simp) a b

def IsHeckeOpFun (X : GenModel gb N) (k : ℕ) (f : G.GAf → ℂ) (a b : ℕ) (T : Module.End ℂ (hodgeH (zs X k) a b)) :
    Prop :=
  ∃ (J : Type) (s : Finset J) (h : J → G.GAf) (c : J → ℂ) (Th : J → Module.End ℂ (hodgeH (zs X k) a b)),
    (∀ i ∈ s, IsHeckeOpZ L X k (h i) a b (Th i)) ∧ f = ∑ i ∈ s, c i • Formalism.UG.dosetInd ℂ (L.KN N) (h i)⁻¹ ∧
      T = ∑ i ∈ s, c i • Th i

variable {L}

end Op

section Away

def IsGoodPrime (G₀ : GDatum) (q : ℕ) [Fact q.Prime] : Prop :=
  Nonempty ((G₀.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 G₀.F] Matrix (Fin G₀.m) (Fin G₀.m) (𝓞 G₀.F ⊗[ℤ] ℤ_[q])) ∧
    (∃ e : ℕ, e.Coprime q ∧ ∀ f : G₀.La →ₗ[ℤ] ℤ, ∃ x, G₀.EF x = e • f) ∧ ¬ (q : ℤ) ∣ NumberField.discr G₀.F

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def awayGrp (G : HTGroup p) (S : Finset ℕ) : Subgroup G.GAf :=
  ⨅ (v : AwayP p) (_ : ∃ q ∈ S, q.Prime ∧ (q : ℤ) ∈ v.1.asIdeal), (ubcMap (AfP.eval v)).ker

variable (L : _root_.GlobalTheory.LKGeo.Link D G)

def awaySupp (N : ℕ) (S : Finset ℕ) : Set G.GAf :=
  {g | ∃ h ∈ awayGrp G S, h ∈ latMonoid L ∧ g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N : Set G.GAf) (L.KN N)}

def heckeAway (N : ℕ) (S : Finset ℕ) : Submodule ℂ (G.GAf → ℂ) :=
  Formalism.UG.Hecke ℂ (L.KN N) ⊓
    { carrier := {f | ∀ g, f g ≠ 0 → g ∈ awaySupp L N S}
      zero_mem' := fun _ h => (h rfl).elim
      add_mem' := fun {f f'} hf hf' g hg => by
        by_cases h : f g = 0
        · exact hf' g fun h' => hg (by simp [h, h'])
        · exact hf g h
      smul_mem' := fun c f hf g hg => hf g fun h => hg (by simp [h]) }

theorem dosetInd_mem_heckeAway {N : ℕ} {S : Finset ℕ} {h : G.GAf} (hS : h ∈ awayGrp G S) (hΔ : h ∈ latMonoid L) :
    Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹ ∈ heckeAway L N S :=
  ⟨Formalism.UG.Final.DosetIndMem _ _ _ _, fun _ hg => ⟨h, hS, hΔ, Set.mem_of_indicator_ne_zero hg⟩⟩

end Away

section Basic₂

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : _root_.GlobalTheory.LKGeo.Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

end Basic₂

end GlobalTheory.W2
