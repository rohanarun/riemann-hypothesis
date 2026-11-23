module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.BaseChange

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

section Pull

open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem exists_gObjMap_pull {b : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S)
    (o : GObj b N s) : ∃ o' : GObj b N (f ≫ s), Nonempty (GObjMap o' o f) := by
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb G.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN G.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  let o' : GObj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A A' f φ (actF o.act) (actF actN) pb
        (fun c => hact _) k x (β.comp (b.t i)) G.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn y
                  onto := fun n hn q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm y => by rw [← map_pow, I.tower n m hn hm]
                  isom := fun n hn y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end Pull

section Cancel

open GlobalTheory.UPel.HT.MapComp

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_cancel {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : GObjMap o₁ o₃ (f ≫ g)) (m₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

end Cancel

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem exists_ext {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] (ψ : R₁ →+* R₂) (β₁ : R₁ →+* R')
    (x : Sp R' ⟶ Sp R₂) (hx : x ≫ spMap ψ = spMap β₁) : ∃ β₂ : R₂ →+* R', x = spMap β₂ ∧ β₁ = β₂.comp ψ := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of R₂) (S := CommRingCat.of R') x
  have e : x = spMap g.hom := hg.symm
  refine ⟨g.hom, e, ?_⟩
  rw [e, ← spMap_comp'] at hx
  have := Spec.map_injective (R := CommRingCat.of R₁) (S := CommRingCat.of R') hx
  exact (congrArg CommRingCat.Hom.hom this).symm

section Rebase

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] {ψ : R₁ →+* R₂}
  {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} (hρ : gb₂.ρ = ψ gb₁.ρ) (ht : ∀ i, gb₂.t i = ψ.comp (gb₁.t i)) {N : ℕ}
  {S : Scheme.{0}} {s₁ : S ⟶ Sp R₁} {s₂ : S ⟶ Sp R₂} (hs : s₂ ≫ spMap ψ = s₁)

def down (o : GObj gb₂ N s₂) : GObj gb₁ N s₁ where
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
  lie := fun R' _ β x hx v hv => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    obtain ⟨w, hw, hv⟩ := o.lie R' β₂ x e v (by rw [hρ]; exact hv)
    exact ⟨w, fun i c => by have := hw i c; rw [ht] at this; exact this, hv⟩
  lieRank := fun k _ _ x β hx i => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    have := o.lieRank k x β₂ e i
    rw [ht] at this
    exact this
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    exact o.geom k x β₂ e

def up (o : GObj gb₁ N s₁) : GObj gb₂ N s₂ where
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
  lie := fun R' _ β x hx v hv => by
    obtain ⟨w, hw, hv⟩ := o.lie R' (β.comp ψ) x (by rw [← hs, ← Category.assoc, hx, spMap_comp']) v
      (by rw [hρ] at hv; exact hv)
    exact ⟨w, fun i c => by rw [ht]; exact hw i c, hv⟩
  lieRank := fun k _ _ x β hx i => by
    rw [ht]
    exact o.lieRank k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp']) i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => o.geom k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp'])

end Rebase

end GlobalTheory.UPel.HT.Gen.BaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPointStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generates_of_close_localEquation_classicalPoint :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
      (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z),
      M₁.IsHom M (AlgHom.id o Ω) π →
      ∀ (U : M.Z.Opens) (D : EffCartierData M.Z),
        (∀ x ∈ (GlobalTheory.EffCartierData.idealSheaf D).support, x ∉ U) →
        ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z),
          M.Cen U x y₀ → ∀ f, EqAt M D x f →
          ∃ k : ℕ, ∀ (G b : M₁.O (π x)),
            ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖RatModel.val M (gPt p ≫ y₀) f‖ →
            b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k →
            (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  intro o Ω _ _ _ _ M₁ M π hπ U D hD x p _ y₀ hy f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set F : Ω := valF M.pt (D.U i) (D.f i)
  set y : Sp (PadicAlgCl p) ⟶ M.Z := gPt p ≫ y₀ with hydef

  have hFO : F ∈ M.O x := RatModel.valF_mem_O hxi _
  have hwx : y (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ x := RatModel.gPt_specializes hy.1 _
  have hwU : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ U := hy.2 ⟨_, rfl⟩
  have hwi : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ D.U i := hwx.mem_open (D.U i).isOpen hxi
  have hwb : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ M.Z.basicOpen (D.f i) := by
    by_contra h
    exact hD _ ((D.mem_support_iff i hwi).2 h) hwU
  have hF0 : RatModel.val M y F ≠ 0 :=
    (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton y (IsLocalRing.closedPoint (PadicAlgCl p)))
      ⟨_, RatModel.valF_mem_O hwi _⟩).2 ((RatModel.isUnit_valF_iff hwi (D.f i)).2 hwb)
  have hFpos : 0 < ‖RatModel.val M y F‖₊ := nnNorm_pos.2 hF0

  have hle : M₁.O (π x) ≤ M.O x := fun c hc => hπ.map_mem_O hc
  let v : M₁.O (π x) →+* PadicAlgCl p :=
    (RatModel.valHomOf y x (RatModel.gPt_specializes hy.1)).comp (Subalgebra.inclusion hle).toRingHom
  have hv_apply : ∀ c : M₁.O (π x), v c = RatModel.val M y c := fun c => rfl
  have hv1 : ∀ c, ‖v c‖₊ ≤ 1 := fun c => by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact RatModel.norm_val_le_one hy.1 (hle c.2)
  have hvlt : ∀ c : M₁.O (π x), ¬ IsUnit c → ‖v c‖₊ < 1 := by
    intro c hc
    have hc' : (c : Ω) ∈ M₁.O (π (y (IsLocalRing.closedPoint (PadicAlgCl p)))) :=
      RatModel.O_le_of_specializes (hwx.map π.continuous) c.2
    have e := hπ.val_comp y (IsLocalRing.closedPoint (PadicAlgCl p)) hc'
    have hc0 : (y₀ ≫ π) (cPt p) = π x := by rw [Scheme.Hom.comp_apply, hy.1]
    have h1 := (RatModel.norm_val_lt_one_iff hc0 c.2).2 hc
    rw [← Category.assoc, ← hydef, e] at h1
    rw [← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact h1

  have : IsDedekindDomain o := ArithBase.ded (Ω := Ω)
  have := M₁.lft
  have : IsLocallyNoetherian M₁.Z := LocallyOfFiniteType.isLocallyNoetherian M₁.s
  have : IsNoetherianRing (M₁.O (π x)) := isNoetherianRing_of_ringEquiv _ (M₁.stalkEquiv (π x))
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal (M₁.O (π x)))
  set ρ : NNReal := s.sup fun c => ‖v c‖₊
  have hρ : ρ < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun c hc => hvlt c ?_
    have : c ∈ maximalIdeal (M₁.O (π x)) := hs ▸ Submodule.subset_span hc
    exact (mem_maximalIdeal c).1 this
  have hm : ∀ c ∈ maximalIdeal (M₁.O (π x)), ‖v c‖₊ ≤ ρ := by
    rw [← hs]
    exact nnnorm_le_of_mem_span v hv1 fun c hc => Finset.le_sup (f := fun c => ‖v c‖₊) hc
  have hspan : Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} = maximalIdeal (M₁.O (π x)) := by
    have : {c : M₁.O (π x) | ¬ IsUnit c} = (maximalIdeal (M₁.O (π x)) : Set (M₁.O (π x))) :=
      Set.ext fun c => (mem_maximalIdeal c).symm
    rw [this, Ideal.span_eq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hFpos hρ
  refine ⟨k, fun G b hGb hb hGf => ?_⟩

  rw [hspan] at hb
  have hbk : ‖RatModel.val M y b‖₊ < ‖RatModel.val M y F‖₊ :=
    lt_of_le_of_lt (nnnorm_le_pow_of_mem_pow v hv1 hm k b hb) hk
  have hadd : RatModel.val M y ((G : Ω) + b) = RatModel.val M y G + RatModel.val M y b :=
    RatModel.val_add (RatModel.gPt_specializes hy.1) (hle G.2) (hle b.2)
  have hGb' : ‖RatModel.val M y G + RatModel.val M y b‖₊ = ‖RatModel.val M y F‖₊ := by
    rw [← hadd]
    exact NNReal.eq hGb
  have hG : ‖RatModel.val M y G‖₊ = ‖RatModel.val M y F‖₊ := by
    refine le_antisymm ?_ ?_
    · have e : RatModel.val M y G = (RatModel.val M y G + RatModel.val M y b) + -RatModel.val M y b := by ring
      rw [e]
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le hGb'.le ?_)
      rw [nnNorm_neg]
      exact hbk.le
    · rw [← hGb']
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le le_rfl ?_)
      by_contra h
      push Not at h
      have := (IsUltrametricDist.nnNorm_add_le_max (RatModel.val M y G) (RatModel.val M y b)).trans
        (max_le h.le le_rfl)
      rw [hGb'] at this
      exact absurd hbk (not_lt.2 this)
  have hG0 : (G : Ω) ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero, nnNorm_zero] at hG
    exact hFpos.ne hG
  have hFne : F ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero] at hF0
    exact hF0 rfl
  refine ⟨hG0, ?_⟩
  have hmul : RatModel.val M y ((G : Ω) / F * F) = RatModel.val M y ((G : Ω) / F) * RatModel.val M y F :=
    RatModel.val_mul (RatModel.gPt_specializes hy.1) hGf hFO
  rw [div_mul_cancel₀ _ hFne] at hmul
  have hq : ‖RatModel.val M y ((G : Ω) / F)‖₊ = 1 := by
    have h2 : ‖RatModel.val M y ((G : Ω) / F)‖₊ * ‖RatModel.val M y F‖₊ = 1 * ‖RatModel.val M y F‖₊ := by
      rw [one_mul, ← nnNorm_mul, ← hmul, hG]
    exact mul_right_cancel₀ hFpos.ne' h2
  have hq' : ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) / F)‖ = 1 := by
    rw [← coe_nnNorm]
    exact congrArg NNReal.toReal hq
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.norm_val_eq_one_iff hy.1 hGf).1 hq')
  simpa [inv_div] using hu.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingPairSectionsNormBounds
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.GenLow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_pos_bounds {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (G : Y → ℝ) (hG : Continuous G)
    (hpos : ∀ y, 0 < G y) : ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y, m ≤ G y ∧ G y ≤ U := by
  rcases isEmpty_or_nonempty Y with h | h
  · exact ⟨1, 1, one_pos, one_pos, fun y => (h.false y).elim⟩
  · obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hG.continuousOn
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hG.continuousOn
    exact ⟨G a, G b, hpos a, hpos b, fun y => ⟨ha (Set.mem_univ y), hb (Set.mem_univ y)⟩⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem continuous_nu (P : Pair p) (a b : ℤ) (M : HermLB p) (hM : P.Rep a b M) (σ : k →+* ℂ)
    (f : X.functionField) (hf : f ∈ P.H a b) : Continuous fun y : CxPts p σ => P.nu a b σ y f := by
  obtain ⟨e, -, hr, hn, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := hr ▸ hf
  have h : (fun y : CxPts p σ => P.nu a b σ y (e u)) = fun y => Real.sqrt ((M.φ σ).nsq (secVal p σ u) y) := by
    funext y
    rw [← hn u σ y, Real.sqrt_sq (nu_nonneg P a b σ y _)]
  rw [h]
  exact ((M.cInf σ).continuous_nsq u).sqrt

theorem gen_low : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧
      (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  intro k _ X _ p D hX P c ⟨n, v, hvH, hnz⟩
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.VolBr.Pair.exists_rep k X p P 0 c
  have hb : ∀ σ : k →+* ℂ, ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y : CxPts p σ,
      m ≤ ∑ i, P.nu 0 c σ y (v i) ∧ ∑ i, P.nu 0 c σ y (v i) ≤ U := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    refine exists_pos_bounds _ (continuous_finsetSum _ fun i _ => continuous_nu P 0 c M hM σ (v i) (hvH i))
      fun y => ?_
    obtain ⟨i, hi⟩ := hnz σ y
    exact lt_of_lt_of_le ((nu_nonneg P 0 c σ y _).lt_of_ne' hi)
      (Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i))
  choose m U hm hU hmU using hb
  have hlow : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ σ, m₀ ≤ m σ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_min m
      exact ⟨m σ, hm σ, hσ⟩
  have hup : ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ σ, U σ ≤ U₀ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_max U
      exact ⟨U σ, hU σ, hσ⟩
  obtain ⟨m₀, hm₀, hm₀le⟩ := hlow
  obtain ⟨U₀, hU₀, hU₀le⟩ := hup
  have hn1 : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by exact_mod_cast lt_max_of_lt_right one_pos
  refine ⟨n, v, min (m₀ / (max n 1 : ℕ)) U₀⁻¹, lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀), fun i => ⟨hvH i, fun σ y => ?_⟩,
    fun σ y => ?_⟩
  · calc P.nu 0 c σ y (v i) ≤ ∑ j, P.nu 0 c σ y (v j) :=
          Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i)
      _ ≤ U σ := (hmU σ y).2
      _ ≤ U₀ := hU₀le σ
      _ = U₀⁻¹⁻¹ := (inv_inv U₀).symm
      _ ≤ (min (m₀ / (max n 1 : ℕ)) U₀⁻¹)⁻¹ :=
          inv_anti₀ (lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀)) (min_le_right _ _)
  · obtain ⟨i₀, -⟩ := hnz σ y
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i₀.elim0
    have hmax : (max n 1 : ℕ) = n := max_eq_left hn
    have hsum : ∑ _j : Fin n, m₀ / (max n 1 : ℕ) ≤ ∑ j, P.nu 0 c σ y (v j) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmax, mul_div_cancel₀ _
        (by exact_mod_cast (show n ≠ 0 by omega))]
      exact (hm₀le σ).trans (hmU σ y).1
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le ⟨i₀, Finset.mem_univ _⟩ hsum
    exact ⟨i, (min_le_left _ _).trans hi⟩

end GlobalTheory.HSNef.GenLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPolarisedChartOfMonomialPreChartSemiAbelianEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem hasPolChart_of_preChart_of_extension : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    IsGrpPullback F.univ.A G j e → abLocus G = Set.range j → PreChart F s j φ BD d x → HasPolChart F s j e φ BD d x :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hG _ he _ h => h.hasPolChart hG he

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j, C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  first | exact @GlobalTheory.FormalAlg.Charts.ev_change | exact GlobalTheory.FormalAlg.Charts.ev_change | (intros; apply GlobalTheory.FormalAlg.Charts.ev_change <;> assumption)
end

