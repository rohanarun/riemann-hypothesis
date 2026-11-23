module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section CForms

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

def rhoC : UF X.E n →* Module.End ℂ (Pol ℂ X.Tau n) := (rhoP lam).comp ((embGL (embAt σ X.emb)).comp (ufGL X.E n))

theorem rhoC_apply (γ : UF X.E n) : rhoC σ lam γ = rhoP lam (embGL (embAt σ X.emb) (ufGL X.E n γ)) := rfl

theorem rhoC_map (γ : UF X.E n) (v : VV X.K lam) :
    rhoC σ lam γ (MvPolynomial.map σ v.1) = MvPolynomial.map σ (rhoV X.emb lam (ufGL X.E n γ) v).1 := by
  refine Eq.trans ?_ (GlobalTheory.ValCmp.use₂ σ lam (embGL X.emb (ufGL X.E n γ)) v.1).symm
  have e : embGL (embAt σ X.emb) (ufGL X.E n γ) = fun τ => Formalism.UG.bc σ (embGL X.emb (ufGL X.E n γ) τ) :=
    funext fun τ => Units.ext rfl
  rw [rhoC_apply, e]
  rfl


variable (ST) in
def cForms (Λ : LevFam X.E X.K n SG) : Submodule ℂ (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol ℂ X.Tau n) where
  carrier := {F | ∀ d, F d ∈ VV ℂ lam ∧ ∀ g : FormG Λ, F (g • d) = σ (Λ.chr g.2 : X.Kˣ) • rhoC σ lam g.1 (F d)}
  add_mem' := by
    intro F G hF hG d
    refine ⟨Submodule.add_mem _ (hF d).1 (hG d).1, fun g => ?_⟩
    simp only [Pi.add_apply]
    rw [(hF d).2 g, (hG d).2 g, map_add (f := _), smul_add]
  zero_mem' := fun d => ⟨Submodule.zero_mem _, fun g => by simp⟩
  smul_mem' := by
    intro r F hF d
    refine ⟨Submodule.smul_mem _ r (hF d).1, fun g => ?_⟩
    simp only [Pi.smul_apply]
    rw [(hF d).2 g, map_smul, smul_comm]

theorem mem_cForms (Λ : LevFam X.E X.K n SG) (F : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol ℂ X.Tau n) : F ∈ cForms ST σ lam Λ ↔
    ∀ d, F d ∈ VV ℂ lam ∧ ∀ (γ : UF X.E n) (h : Λ.grp),
      F ((γ, (h.1 : GLG (E := X.E) (n := n) (SG := SG))) • d) = σ (Λ.chr h : X.Kˣ) • rhoC σ lam γ (F d) :=
  forall_congr' fun _ => and_congr_right fun _ => ⟨fun h γ k => h (γ, k), fun h g => h g.1 g.2⟩

def toCForm (L : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG) :
    (formGSD (squarePk X lam L) Λ).EqFun →ₛₗ[σ] cForms ST σ lam Λ where
  toFun φ := ⟨fun d => MvPolynomial.map σ (φ.1 d).1, fun d => ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ (φ.1 d).2, fun g => by
    have h : (φ.1 (g • d)).1 = ((Λ.chr g.2 : X.Kˣ) : X.K) • (rhoV X.emb lam (ufGL X.E n g.1) (φ.1 d)).1 :=
      congrArg Subtype.val (φ.2 g d)
    refine Eq.trans ?_ (congrArg (σ (Λ.chr g.2 : X.Kˣ) • ·) (rhoC_map σ lam g.1 (φ.1 d)).symm)
    exact (congrArg (MvPolynomial.map σ) h).trans ((mapS σ).map_smulₛₗ _ _)⟩⟩
  map_add' φ ψ := Subtype.ext (funext fun d => map_add (MvPolynomial.map σ) (φ.1 d).1 (ψ.1 d).1)
  map_smul' c φ := Subtype.ext (funext fun d => (mapS σ).map_smulₛₗ c (φ.1 d).1)

theorem toCForm_injective (L : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG) :
    Function.Injective (toCForm σ lam L Λ) := fun _ _ h =>
  Subtype.ext (funext fun d => Subtype.ext (MvPolynomial.map_injective σ σ.injective (congrFun (congrArg Subtype.val h) d)))

theorem tr_mem_cForms (Λ : LevFam X.E X.K n SG) (a : GLG (E := X.E) (n := n) (SG := SG)) (ha : ∀ w, (Λ w).NormBy (a w))
    {F : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol ℂ X.Tau n} (hF : F ∈ cForms ST σ lam Λ) :
    (fun d => F (((1 : UF X.E n), a⁻¹) • d)) ∈ cForms ST σ lam Λ := by
  rw [mem_cForms] at hF ⊢
  refine fun d => ⟨(hF _).1, fun γ h => ?_⟩
  obtain ⟨h', e1, e2⟩ := Λ.normBy a ha h
  have h1 := (hF (((1 : UF X.E n), a⁻¹) • d)).2 γ h'
  rw [smul_smul, Prod.mk_mul_mk, mul_one] at h1
  rw [smul_smul, Prod.mk_mul_mk, one_mul, e1, h1, e2]


variable (ST) in
def cTr (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w)) :
    Representation ℂ A (cForms ST σ lam Λ) where
  toFun a :=
    { toFun := fun F => ⟨_, tr_mem_cForms σ lam Λ (ι a) (hι a) F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext (funext fun d => ?_)
    show F.1 (((1 : UF X.E n), (ι 1)⁻¹) • d) = F.1 d
    rw [map_one, inv_one, ← Prod.one_eq_mk, one_smul]
  map_mul' a b := by
    refine LinearMap.ext fun F => Subtype.ext (funext fun d => ?_)
    show F.1 (((1 : UF X.E n), (ι (a * b))⁻¹) • d) = F.1 (((1 : UF X.E n), (ι b)⁻¹) • ((1 : UF X.E n), (ι a)⁻¹) • d)
    rw [smul_smul, Prod.mk_mul_mk, one_mul, map_mul, mul_inv_rev]

theorem mem_cForms_split {r : ℕ} {SG0 : Finset (HeightOneSpectrum (𝓞 X.E))} {ι : GLG (E := X.E) (n := r) (SG := SG0) →* GLG (E := X.E) (n := n) (SG := SG)}
    {ΛP ΛK : LevFam X.E X.K n SG} {Λ0 : LevFam X.E X.K r SG0} (H : LevFam.Split ι ΛP ΛK Λ0)
    (F : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol ℂ X.Tau n) :
    F ∈ cForms ST σ lam ΛP ↔ F ∈ cForms ST σ lam ΛK ∧
      ∀ (a : Λ0.grp) d, F (((1 : UF X.E n), (ι a.1)⁻¹) • d) = σ ((Λ0.chr a)⁻¹ : X.Kˣ) • F d := by
  rw [mem_cForms, mem_cForms]
  constructor
  · intro hφ
    refine ⟨fun d => ⟨(hφ d).1, fun γ k => ?_⟩, fun a d => ?_⟩
    · obtain ⟨hm, e⟩ := H.sub k
      rw [← e]
      exact (hφ d).2 γ ⟨k.1, hm⟩
    · obtain ⟨hm, e⟩ := H.emb a⁻¹
      have h1 := (hφ d).2 1 ⟨_, hm⟩
      rw [e, map_one, map_inv] at h1
      rw [← map_inv]
      exact h1
  · rintro ⟨h1, h2⟩ d
    refine ⟨(h1 d).1, fun γ h => ?_⟩
    obtain ⟨a, k, e1, e2⟩ := H.fac h
    have h3 := h2 a⁻¹ ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) • d)
    rw [(h1 d).2 γ k, smul_smul, Prod.mk_mul_mk, one_mul, map_inv Λ0.chr, inv_inv] at h3
    have e3 : (ι ((a⁻¹ : ↥Λ0.grp) : GLG (E := X.E) (n := r) (SG := SG0)))⁻¹ = ι a.1 := by
      rw [Subgroup.coe_inv, map_inv, inv_inv]
    rw [e3] at h3
    rw [e1, h3, e2, smul_smul, Units.val_mul, map_mul]

def FrLaw (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (H : Subgroup (FrmG Λ Θ))
    (F : DecoF X.E n ST SG Q → Pol ℂ X.Tau n) : Prop :=
  ∀ p, F p ∈ VV ℂ lam ∧ ∀ g ∈ H, F (g • p) = (σ (Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ))⁻¹ • rhoC σ lam g.1 (F p)

structure IsSubLev (Λ Λ' : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (H : Subgroup (FrmG Λ Θ)) : Prop where

  mem : ∀ g, g ∈ H ↔ g.2.1.1 ∈ Λ'.grp

  sub : ∀ k : Λ'.grp, ∃ hm : k.1 ∈ Λ.grp, Λ.chr ⟨_, hm⟩ = Λ'.chr k

theorem isSubLev_top (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : IsSubLev Λ Λ Θ ⊤ :=
  ⟨fun g => iff_of_true trivial g.2.1.2, fun k => ⟨k.2, rfl⟩⟩

variable {Λ Λ' : LevFam X.E X.K n SG} {Θ : LevFam X.E X.K n Q} {H : Subgroup (FrmG Λ (levRedFam Θ))}
  (hH : IsSubLev Λ Λ' (levRedFam Θ) H) (hd : Disjoint SG Q)
include hH hd

theorem frLaw_comp_iff (F : DecoSet (E := X.E) (n := n) (ST := ST) (SG := uSG SG Q) → Pol ℂ X.Tau n) :
    FrLaw σ lam Λ (levRedFam Θ) H (fun p => F (forgetFr p)) ↔ F ∈ cForms ST σ lam (Λ'.glue Θ).inv := by
  have key : ∀ (g : FrmG Λ (levRedFam Θ)) (hg : g.2.1.1 ∈ Λ'.grp), (σ (Λ.chr g.2.1 * (levRedFam Θ).chr g.2.2 : X.Kˣ))⁻¹ =
      σ ((Λ'.glue Θ).inv.chr (redFG Λ' Θ (g.1, ⟨_, hg⟩, g.2.2)).2 : X.Kˣ) := fun g hg => by
    obtain ⟨hm, e⟩ := hH.sub ⟨_, hg⟩
    have e' : Λ.chr g.2.1 = Λ'.chr ⟨_, hg⟩ := e
    rw [e', chr_redFG Λ' Θ hd (g.1, ⟨_, hg⟩, g.2.2), Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  constructor
  · intro h d
    obtain ⟨p, rfl⟩ := forgetFr_surjective d
    refine ⟨(h p).1, fun a => ?_⟩
    obtain ⟨g, rfl⟩ := redFG_surjective Λ' Θ a
    obtain ⟨hm, -⟩ := hH.sub g.2.1
    have h1 := (h p).2 (g.1, ⟨_, hm⟩, g.2.2) ((hH.mem _).2 g.2.1.2)
    rw [key _ g.2.1.2] at h1
    rw [← forgetFr_frm_smul]
    exact h1
  · intro h p
    refine ⟨(h _).1, fun g hg => ?_⟩
    have h1 := (h (forgetFr p)).2 (redFG Λ' Θ (g.1, ⟨_, (hH.mem g).1 hg⟩, g.2.2))
    rw [← forgetFr_frm_smul] at h1
    rw [key g ((hH.mem g).1 hg)]
    exact h1

theorem FrLaw.eq_of_forgetFr_eq {F : DecoF X.E n ST SG Q → Pol ℂ X.Tau n} (h : FrLaw σ lam Λ (levRedFam Θ) H F)
    {p q : DecoF X.E n ST SG Q} (e : forgetFr p = forgetFr q) : F p = F q := by
  obtain ⟨g, h1, h2⟩ := exists_redFG_smul Λ Θ hd 1 p q ((one_smul _ _).trans e)
  have h3 : g.2.1.1 = 1 := funext fun w =>
    (redGQ_of_mem (g.2.1.1, g.2.2.1) (inLeft Q w) w.2).symm.trans (congrFun (congrArg (fun x => x.2.1) h1) (inLeft Q w))
  have h4 : g.1 = 1 := congrArg (fun x : FormG (Λ.glue Θ).inv => x.1) h1
  have h5 := (h p).2 g ((hH.mem g).2 (h3 ▸ one_mem _))
  rw [h2, chr_redFG Λ Θ hd g, h1, h4] at h5
  simpa using h5.symm

theorem FrLaw.exists_form {F : DecoF X.E n ST SG Q → Pol ℂ X.Tau n} (h : FrLaw σ lam Λ (levRedFam Θ) H F) :
    ∃ G ∈ cForms ST σ lam (Λ'.glue Θ).inv, ∀ p, G (forgetFr p) = F p := by
  have e : ∀ p, F (Function.surjInv forgetFr_surjective (forgetFr p)) = F p := fun p =>
    h.eq_of_forgetFr_eq σ lam hH hd (Function.surjInv_eq _ _)
  refine ⟨fun d => F (Function.surjInv forgetFr_surjective d), (frLaw_comp_iff σ lam hH hd _).1 ?_, e⟩
  rwa [funext e]

end CForms

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem lamT_eq (u : Pr.Word) (j : ℕ) : lamT (W.hc u) j = W.lamTrue u j := rfl

def MtC : Submodule ℂ (RowPt Pr R sel mu → Pol ℂ X.Tau (R.N R.m - 1)) := cForms ∅ σ W.sgTrue (rowTyKK Ch sel mu).inv

def MtP : Submodule ℂ (RowPt Pr R sel mu → Pol ℂ X.Tau (R.N R.m - 1)) := cForms ∅ σ W.sgTrue (rowTy Ch sel mu P).inv

def rightTranslationAction : Representation ℂ (G0 X.E Pr.vGs R.r) (MtC W Ch sel mu σ) :=
  cTr ∅ σ W.sgTrue _ (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R)) (rowTyKK_inv_normBy_g0Hat Ch sel mu)

theorem mem_MtP_iff (F : RowPt Pr R sel mu → Pol ℂ X.Tau (R.N R.m - 1)) : F ∈ MtP W Ch sel mu P σ ↔
    ∃ h : F ∈ MtC W Ch sel mu σ, ∀ a : P.grp,
      rightTranslationAction W Ch sel mu σ a.1 ⟨F, h⟩ = σ (P.chr a : X.Kˣ) • (⟨F, h⟩ : MtC W Ch sel mu σ) := by
  refine (mem_cForms_split σ W.sgTrue (rowTy_split Ch sel mu P).inv F).trans ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a => Subtype.ext (funext fun d => ?_)⟩
    have := h2 ⟨a.1, a.2⟩ d
    rw [P.inv_chr a, inv_inv] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a d => ?_⟩
    have := congrFun (congrArg Subtype.val (h2 ⟨a.1, a.2⟩)) d
    rw [P.inv_chr ⟨a.1, a.2⟩, inv_inv]
    exact this

theorem MtP_le_MtC : MtP W Ch sel mu P σ ≤ MtC W Ch sel mu σ := fun F h => ((mem_MtP_iff W Ch sel mu P σ F).1 h).1

def toMtP : MtildeV W Ch sel mu P →ₛₗ[σ] MtP W Ch sel mu P σ := toCForm σ W.sgTrue _ _

theorem toMtilde_injective : Function.Injective (toMtP W Ch sel mu P σ) := toCForm_injective σ W.sgTrue _ _

def rowKH : Subgroup (FrmG (rowTyG Ch P) (levQX R sel mu)) :=
  (rowTyK Ch).grp.comap ((rowTyG Ch P).grp.subtype.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)))

end Rows

section Per

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

def idxTop : Idx sel mu L R.m := ⟨none, by simp⟩


variable (R) in
theorem ysAt_m : ysAt R sel mu cst R.m = Ys.triv X _ := if_neg (Nat.succ_ne_self _)

def topPt (u : Pr.Word) (p : ChPt (R := R) sel mu u R.m) :
    PtY (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) (ysAt R sel mu cst R.m) :=
  ⟨(p, ∅), by rw [ysAt_m]; rfl⟩

theorem topPt_val (u : Pr.Word) (p : PtY (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) (ysAt R sel mu cst R.m)) :
    topPt sel mu cst u p.1.1 = p := by
  have h := p.2
  rw [congrArg (fun y => y.ys p.1.1.deco.1.N) (ysAt_m R sel mu cst)] at h
  exact Subtype.ext (Prod.ext rfl (Eq.symm h))

variable (u : Pr.Word)
  (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L (topLev Ch sel mu cst P) u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L (topLev Ch sel mu cst P) u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L (topLev Ch sel mu cst P) u i).D b →
    (stepAt sel mu cst L (topLev Ch sel mu cst P) u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)

def perAtH (H : Subgroup (FrmG (rowTyG Ch P) (levQX R sel mu))) :
    PerIn (chainAt sel mu cst L (topLev Ch sel mu cst P) u rho rho' cD Th) where
  S' := stepX Ch sel mu P
  b0 := idxTop sel mu L
  til _ p := topPt sel mu cst u (tilF sel mu u p.1.1)
  ext _ := extTop Ch sel mu cst P
  sg := W.sgW
  tz := star ((Pr.piT u : 𝓞 X.E) : X.E)
  H _ := H

def perAt : PerIn (chainAt sel mu cst L (topLev Ch sel mu cst P) u rho rho' cD Th) :=
  perAtH W Ch sel mu cst L P u rho rho' cD Th ⊤

section Gen

variable (H : Subgroup (FrmG (rowTyG Ch P) (levQX R sel mu))) (σ : X.K →+* ℂ)

variable {H} {Λ' : LevFam X.E X.K (R.N R.m - 1) Pr.vGs} (hH : IsSubLev (rowTyG Ch P) Λ' (levQX R sel mu) H)
  (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

end Gen

variable (σ : X.K →+* ℂ)

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

end Per

end GlobalTheory.Mem.Col2
