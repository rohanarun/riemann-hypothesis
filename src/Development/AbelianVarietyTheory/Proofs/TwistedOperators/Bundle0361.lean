module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbases
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {T : Type} [CommRing T]
    (s : Sp (DualNumber T) ⟶ Y) (x₀ : Sp T ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber T) ⟶ X,
      spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber T) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom T T T).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber T, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  exact GlobalTheory.existsUnique_lift_of_etale_of_surjective f π hπ hnil x₀ s h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

variable {T : Type} [CommRing T]

abbrev epsBase (T : Type) [CommRing T] : Sp (DualNumber T) ⟶ Sp T := spMap (algebraMap T (DualNumber T))

abbrev epsZero (T : Type) [CommRing T] : Sp T ⟶ Sp (DualNumber T) := spMap (TrivSqZeroExt.fstHom T T T).toRingHom

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epsZero_base : epsZero T ≫ epsBase T = 𝟙 _ := by
  rw [spMap_spMap]
  exact (congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id _)

theorem eps_base (a : T) : spMap (epsMul a) ≫ epsBase T = epsBase T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsZero_eps (a : T) : epsZero T ≫ spMap (epsMul a) = epsZero T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  simp [epsMul]

theorem eps_comm (a b : T) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_spMap, spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, mul_left_comm]

theorem eps_cancel {a b : T} (h : a * b = 1) : spMap (epsMul a) ≫ spMap (epsMul b) = 𝟙 _ := by
  have : (epsMul a).comp (epsMul b) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, ← _root_.mul_assoc, h]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  exact Spec.map_id _

abbrev zeroAt (x : Sp T ⟶ Xo.X) : (Over.mk x : Over Xo.X) ⟶ tEps x := sec' x (epsZero T) epsZero_base

abbrev scaleAt (x : Sp T ⟶ Xo.X) (a : T) : tEps x ⟶ tEps x := res x (spMap (epsMul a)) (eps_base a)

theorem zeroAt_scaleAt (x : Sp T ⟶ Xo.X) (a : T) : zeroAt x ≫ scaleAt x a = zeroAt x :=
  Over.OverMorphism.ext (epsZero_eps a)

theorem scaleAt_comm (x : Sp T ⟶ Xo.X) (a b : T) : scaleAt x a ≫ scaleAt x b = scaleAt x b ≫ scaleAt x a :=
  Over.OverMorphism.ext (eps_comm a b)

theorem isTanAt_iff {x : Sp T ⟶ Xo.X} (a : tEps x ⟶ Xo.univ.t.G) : IsTanAt x a.left ↔ zeroAt x ≫ a = 1 :=
  ⟨fun h => Over.OverMorphism.ext h.2, fun h => ⟨Over.w a, congrArg (·.left) h⟩⟩

theorem isEigAt_iff {c : Coeff l} [Algebra c.F T] {x : Sp T ⟶ Xo.X} (τ : E →+* ℂ) (a : tEps x ⟶ Xo.univ.t.G) :
    IsEigAt c τ a.left ↔ ∀ r : 𝓞 E, a ≫ Xo.univ.t.act.act r = scaleAt x (algebraMap c.F T (embK c τ r)) ≫ a :=
  forall_congr' fun _ => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩

theorem isCombAt_iff {x : Sp T ⟶ Xo.X} {m : ℕ} (a : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → T)
    (b : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun i => (a i).left) cf b.left ↔ (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod = b := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain rfl : u = fun i => scaleAt x (cf i) ≫ a i := funext fun i => Over.OverMorphism.ext (hu i)
    exact Over.OverMorphism.ext h
  · intro h
    exact ⟨_, fun _ => rfl, congrArg (·.left) h⟩

variable {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'}

def tanMap (h : IsLinHom Ψ) : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ (epsBase T) a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem tanMap_left (h : IsLinHom Ψ) (a : tEps x ⟶ Xo.univ.t.G) : (tanMap h a).left = push Ψ (epsBase T) a := rfl

theorem tanMap_scale (h : IsLinHom Ψ) (s : T) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (scaleAt x s ≫ a) = scaleAt x' s ≫ tanMap h a :=
  Over.OverMorphism.ext (push_res Ψ _ _ a)

theorem tanMap_act (h : IsLinHom Ψ) (r : 𝓞 E) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (a ≫ Xo.univ.t.act.act r) = tanMap h a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x (epsBase T) (a ≫ Xo.univ.t.act.act r) =
      toFib x (epsBase T) a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, tanMap_left, tanMap_left, push, push, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

theorem sends_one (h : IsLinHom Ψ) : Sends Ψ 1 1 := by
  obtain ⟨f, hf, -⟩ := exists_pointHom h
  simpa using hf 1

theorem tanMap_zero (h : IsLinHom Ψ) {a : tEps x ⟶ Xo.univ.t.G} (ha : zeroAt x ≫ a = 1) :
    zeroAt x' ≫ tanMap h a = 1 :=
  Over.OverMorphism.ext ((sends_sec'_iff h.1 (epsZero T) epsZero_base a 1).1 (by rw [ha]; exact sends_one h))

theorem existsUnique_tanMap (h : IsLinHom Ψ) [Etale Ψ] {w : tEps x' ⟶ Xo.univ.t.G} (hw : zeroAt x' ≫ w = 1) :
    ∃! a : tEps x ⟶ Xo.univ.t.G, zeroAt x ≫ a = 1 ∧ tanMap h a = w := by
  have e₀ : ∀ (y : Sp T ⟶ Xo.X) (a : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ a = 1 ↔
      epsZero T ≫ toFib y (epsBase T) a = (lift (𝟙 (Over.mk y)) (1 : Over.mk y ⟶ Xo.univ.t.G)).left := fun y a => by
    rw [← lift_sec' y _ epsZero_base]
    refine ⟨fun e => by rw [← e], fun e => Over.OverMorphism.ext ?_⟩
    rw [← lift_l_snd (𝟙 (Over.mk y)) (_ ≫ a), e, lift_l_snd]
  have e₁ : ∀ a : tEps x ⟶ Xo.univ.t.G, tanMap h a = w ↔ toFib x (epsBase T) a ≫ Ψ = toFib x' (epsBase T) w :=
    fun a => by
      refine ⟨fun e => gx_ext ?_ ?_, fun e => Over.OverMorphism.ext ?_⟩
      · rw [Category.assoc, h.1, toFib_fst, toFib_fst]
      · rw [toFib_snd, ← e, tanMap_left, push, Category.assoc]
      · rw [tanMap_left, push, reassoc_of% e, toFib_snd]
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift Ψ (toFib x' (epsBase T) w)
    (lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ((sends_one h).trans ((e₀ x' w).1 hw).symm)
  have hv : v ≫ (fst (Over.mk x) Xo.univ.t.G).left = epsBase T := by rw [← h.1, reassoc_of% h₂, toFib_fst]
  let a : tEps x ⟶ Xo.univ.t.G := Over.homMk (v ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hv]; rfl)
  have ha : toFib x (epsBase T) a = v := gx_ext (by rw [toFib_fst, hv]) (by rw [toFib_snd]; rfl)
  refine ⟨a, ⟨(e₀ x a).2 (by rw [ha, h₁]), (e₁ a).2 (by rw [ha, h₂])⟩, fun b hb => Over.OverMorphism.ext ?_⟩
  rw [← toFib_snd x _ b, hu _ ⟨(e₀ x b).1 hb.1, (e₁ b).1 hb.2⟩]
  rfl

theorem exists_basis_image {c : Coeff l} [Algebra c.F T] (h : IsLinHom Ψ) [Etale Ψ] {p : ℕ} {q : T}
    (hq : q * p = 1) (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left))
    (tan : ∀ i, IsTanAt x (u i)) (eig : ∀ i, IsEigAt c τ (u i))
    (basis : ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x u a w) :
    ∃ u' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ i, IsLieImg p Ψ (u i) (u' i)) ∧
      (∀ i, IsEigAt c τ (u' i)) ∧ ∀ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x' u' a w := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → (tEps x ⟶ Xo.univ.t.G), u = fun i => (a i).left :=
    ⟨fun i => Over.homMk (u i) (tan i).1, rfl⟩
  have c₁ : ∀ y : Sp T ⟶ Xo.X, scaleAt y q ≫ scaleAt y p = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel hq)
  have c₂ : ∀ y : Sp T ⟶ Xo.X, scaleAt y p ≫ scaleAt y q = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel ((mul_comm _ _).trans hq))
  let L : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' q ≫ tanMap h b) fun b b' => by rw [map_mul, MonObj.comp_mul]
  have hL : ∀ b, L b = scaleAt x' q ≫ tanMap h b := fun _ => rfl
  have zs : ∀ (y : Sp T ⟶ Xo.X) (s : T) (b : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ b = 1 →
      zeroAt y ≫ scaleAt y s ≫ b = 1 := fun y s b hb => by rw [← Category.assoc, zeroAt_scaleAt, hb]
  have Lz : ∀ b, zeroAt x ≫ b = 1 → zeroAt x' ≫ L b = 1 := fun b hb => zs _ _ _ (tanMap_zero h hb)
  have Ls : ∀ s b, L (scaleAt x s ≫ b) = scaleAt x' s ≫ L b := fun s b => by
    rw [hL, hL, tanMap_scale, ← Category.assoc, scaleAt_comm, Category.assoc]
  have La : ∀ r b, L (b ≫ Xo.univ.t.act.act r) = L b ≫ Xo.univ.t.act.act r := fun r b => by
    rw [hL, hL, tanMap_act, Category.assoc]
  have Li : ∀ b b', zeroAt x ≫ b = 1 → zeroAt x ≫ b' = 1 → L b = L b' → b = b' := fun b b' hb hb' e => by
    have e' := congrArg (scaleAt x' p ≫ ·) e
    simp only [hL, reassoc_of% (c₂ x')] at e'
    exact (existsUnique_tanMap h (tanMap_zero h hb')).unique ⟨hb, e'⟩ ⟨hb', rfl⟩
  have ta : ∀ i, zeroAt x ≫ a i = 1 := fun i => (isTanAt_iff _).1 (tan i)
  refine ⟨fun i => (L (a i)).left, fun i => ⟨tan i, (isTanAt_iff _).2 (Lz _ (ta i)), a i, rfl, ?_⟩,
    fun i => (isEigAt_iff τ _).2 fun r => ?_, fun w hw hw' => ?_⟩
  · exact congrArg (·.left) (show scaleAt x' p ≫ L (a i) = tanMap h (a i) by rw [hL, reassoc_of% (c₂ x')])
  · rw [← La, (isEigAt_iff τ _).1 (eig i), Ls]
  · obtain ⟨w, rfl⟩ : ∃ b : tEps x' ⟶ Xo.univ.t.G, w = b.left := ⟨Over.homMk w hw.1, rfl⟩
    obtain ⟨v, ⟨hv, e⟩, -⟩ := existsUnique_tanMap h (zs x' p w ((isTanAt_iff _).1 hw))
    obtain rfl : L v = w := by rw [hL, e, reassoc_of% (c₁ x')]
    have ev : IsEigAt c τ v.left := (isEigAt_iff τ _).2 fun r => Li _ _
      (by have := Xo.univ.t.act.hom r; rw [← Category.assoc, hv, MonObj.one_comp]) (zs _ _ _ hv)
      (by rw [La, Ls, (isEigAt_iff τ _).1 hw'])
    refine (existsUnique_congr fun cf => ?_).1 (basis _ ((isTanAt_iff _).2 hv) ev)
    have e : L (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod =
        (List.ofFn fun i => scaleAt x' (cf i) ≫ L (a i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Ls _ _)
    rw [isCombAt_iff, isCombAt_iff, ← e]
    refine ⟨congrArg L, Li _ _ (LieEtale.comp_listProd _ _ fun b hb => ?_) hv⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact zs _ _ _ (ta i)

end GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem GlobalTheory.HeckePointLawRing.exists_frame_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T]
    (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ →
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
      (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧
      ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  intro E _ _ _ H Dw l Xo c T _ _ y x' Ψ p hp h het
  have hF : ((p : c.F)) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hq : algebraMap c.F T ((p : c.F)⁻¹) * (p : T) = 1 := by
    rw [← map_natCast (algebraMap c.F T) p, ← map_mul, inv_mul_cancel₀ hF, map_one]
  choose u h₁ h₂ h₃ using fun τ => GlobalTheory.HeckePointLawRing.exists_basis_image (c := c) h hq τ
    (y.u τ) (y.tan τ) (y.eig τ) (y.basis τ)
  exact ⟨u, h₁, h₂, h₃⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < c.m, LNe c (c.χ k) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ c.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

theorem chainUp_of : ∀ D : D7, MetEx D → ParBound D → ChainL D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = c.n := by rw [hs₀.rank]; simp
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

theorem ontoAll_of : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hPB hSU c hc s₀ hs₀ k hk s Θ hR
  have hUp := chainUp_of D hMet hPB (_root_.GlobalTheory.EvenOnto.chainL_and_inj D).1 hSU
  obtain ⟨hs, hadj⟩ := hUp c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := (_root_.GlobalTheory.EvenOnto.vanish_and_parLin D hMet).2 c s₀
  refine _root_.GlobalTheory.ChainOnto.surjective_of_adjoint_separates (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact (_root_.GlobalTheory.EvenOnto.chainL_and_inj D).2 c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinBumpAdj

variable {D : D7}

theorem infPart_conj_eq_zero {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  rw [e, h, map_zero]

theorem adj_fin {m n : ℕ} {x : Mx D m n} (h : x.map (infPart D) = 0) : (adj x).map (infPart D) = 0 := by
  funext i j
  exact infPart_conj_eq_zero (a := x j i) (congrFun (congrFun h j) i)

theorem smul_fin {m n : ℕ} (c : AE D) {x : Mx D m n} (h : x.map (infPart D) = 0) : (c • x).map (infPart D) = 0 := by
  funext i j
  show infPart D (c * x i j) = 0
  rw [map_mul, show infPart D (x i j) = 0 from congrFun (congrFun h i) j, mul_zero]

theorem continuous_smul_mx {X : Type} [TopologicalSpace X] {m n : ℕ} (c : AE D) {f : X → Mx D m n} (hf : Continuous f) :
    Continuous fun x => c • f x :=
  continuous_matrix fun i j => continuous_const.mul (hf.matrix_elem i j)

variable (S : HSp D) (σ : ℕ)

def adjMap : Mx D S.rank σ →+ Mx D σ S.rank where
  toFun y := incA D (-D.host.xi0⁻¹) • (adj y * gA S)
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add]

def adjInv (η : Mx D σ S.rank) : Mx D S.rank σ := incA D D.host.xi0 • (giA S * adj η)

theorem adjMap_apply (y : Mx D S.rank σ) : adjMap S σ y = incA D (-D.host.xi0⁻¹) • (adj y * gA S) := rfl

theorem adjInv_adjMap (y : Mx D S.rank σ) : adjInv S σ (adjMap S σ y) = y := by
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, giA_gA_cancel, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul]

theorem adjMap_adjInv (η : Mx D σ S.rank) : adjMap S σ (adjInv S σ η) = η := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    have h1 := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
    rw [map_mul, map_one, GlobalTheory.DualPairCheck.cA_cA] at h1
    rw [mul_comm, h1]
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_giA, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one, smul_smul, h, one_smul]

theorem continuous_adjMap : Continuous (adjMap S σ) :=
  continuous_smul_mx _ (f := fun y : Mx D S.rank σ => (adj y * gA S : Mx D σ S.rank))
    (continuous_adj.matrix_mul continuous_const)

theorem continuous_adjInv : Continuous (adjInv S σ) :=
  continuous_smul_mx _ (f := fun η : Mx D σ S.rank => (giA S * adj η : Mx D S.rank σ))
    (continuous_const.matrix_mul continuous_adj)

theorem adjMap_fin {y : Mx D S.rank σ} (h : y.map (infPart D) = 0) : (adjMap S σ y).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.zero_mul])

theorem adjInv_fin {η : Mx D σ S.rank} (h : η.map (infPart D) = 0) : (adjInv S σ η).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.mul_zero])

theorem finLat_comap {B : AddSubgroup (Mx D σ S.rank)} (hB : FinLat B) : FinLat (B.comap (adjMap S σ)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← adjInv_adjMap S σ a]
    exact (GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjInv_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hB.fin _ ha)))
  · have e : ((B.comap (adjMap S σ) : AddSubgroup _) : Set (Mx D S.rank σ)) = adjInv S σ '' (B : Set _) := by
      ext a
      constructor
      · intro ha
        exact ⟨_, ha, adjInv_adjMap S σ a⟩
      · rintro ⟨η, hη, rfl⟩
        show adjMap S σ (adjInv S σ η) ∈ B
        rw [adjMap_adjInv]
        exact hη
    rw [e]
    exact hB.cpt.image (continuous_adjInv S σ)
  · obtain ⟨U, hU, h0, hUB⟩ := hB.opn
    refine ⟨adjMap S σ ⁻¹' U, hU.preimage (continuous_adjMap S σ), by rw [Set.mem_preimage, map_zero]; exact h0,
      fun a ha hf => ?_⟩
    exact hUB _ ha ((GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjMap_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 hf)))

theorem exists_bump_adj : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  intro D V₀ W W₀ σ dW B₂ hB y
  obtain ⟨b, hb, hby, -, hs, hp⟩ := exists_bump_le y (B₂.comap (adjMap V₀ σ)) (finLat_comap V₀ σ hB) Set.univ Filter.univ_mem
  refine ⟨fun z => (b z : ℂ), hb, by simp [hby], fun η hη c hc z => ?_, fun z hz => ?_⟩
  · have h1 : dW.pY * (dW.jY * adjMap V₀ σ c) = dW.pY * (dW.jY * η) := congrArg (fun w : WO V₀ W => dW.pY * (show Mx D W.rank V₀.rank from w)) hc
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dW.pY_jY, Matrix.one_mul, Matrix.one_mul] at h1
    have h2 : c ∈ B₂.comap (adjMap V₀ σ) := by
      rw [AddSubgroup.mem_comap, h1]; exact hη
    beta_reduce
    rw [hp c h2 z]
  · obtain ⟨r, hr, -, hz'⟩ := hs z (fun h => hz (by simp [h]))
    exact ⟨r, hr, _, hz', rfl⟩

end GlobalTheory.AscFinBumpAdj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBlocStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  first | exact @GlobalTheory.DblVacUnip.exists_unip | exact GlobalTheory.DblVacUnip.exists_unip | (intros; apply GlobalTheory.DblVacUnip.exists_unip <;> assumption)
end

