<?php
  include('handleurl.php');
  include('top.inc.php');

  if ($pagename == "home") {
    if ($lang == "en") {
      ?>

      <div id="news"><h3>News</h3>

	  <p>[2010-11] COQTAIL is now a junior lab funded by the <a href="http://www.ens-lyon.fr">ENS Lyon</a>.</p>
      <p>[07 april 2010] The first release is now available! You can download it <a href="http://sourceforge.net/projects/coqtail/files/">here</a>.</p>
      </div>

      <h2>Origin &amp; Objectives</h2>

      <p>The <a href="https://sourceforge.net/projects/coqtail/">COQTAIL</a> project is the biological
      son of the workpackage `Proofs` of the <a href="http://graal.ens-lyon.fr/coquille">COQUILLE</a>
      project. It is therefore based on all the results obtained during the development of COQUILLE.</p>

      <p>In addition to implementing tools dedicated to the easy formalization of mathematics as we see
      them in french <i>Classes préparatoires</i>, this project will proove licence-level results.</p>

      <h2>Development axis</h2>

      <ul>
        <li>Analysis (real and complex)</li>
        <li>Arithmetic</li>
        <li>Calculability</li>
        <li>&#x2102; implementation</li>
        <li>Logic and &#x211d; axiomatic expressivity</li>
        <li>Topology</li>
      </ul>
      <?php
    } elseif ($lang == "fr") {
      ?>
      <div id="news"><h3>News</h3>

	  <p>[2010-11] COQTAIL est maintenant un laboratoire junior de l'<a href="http://www.ens-lyon.fr">ENS Lyon</a>.</p>
      <p>[07 avril] La première révision est maintenant disponible ! Vous pouvez la télécharger <a href="http://sourceforge.net/projects/coqtail/files/">ici</a>.</p>
      </div>

      <h2>Origine &amp; Objectifs</h2>

      <p>Le projet <a href="https://sourceforge.net/projects/coqtail/">COQTAIL</a> est le fils biologique du groupe de travail `Preuves` du projet
      <a href="http://graal.ens-lyon.fr/coquille">COQUILLE</a>. Il se fonde donc sur
      l'intégralité des résultats obtenus lors du semestre de développement de COQUILLE.</p>

      <p>En plus d'implémenter des outils permettant une formalisation aisée des mathématiques
      abordées en classes préparatoires, ce projet tâchera également de démontrer des résultats
      de niveau licence.</p>

      <h2>Axes de développements</h2>

      <ul>
        <li>Analyse (réelle et complexe)</li>
        <li>Arithmétique</li>
        <li>Calculabilité</li>
        <li>Implémentation de &#x2102;</li>
        <li>Logique, expressivité de l'axiomatique de &#x211d;</li>
        <li>Topologie</li>
      </ul>
      <?php
    }
  }

  elseif($pagename == "team") {
    if ($lang == "en") {
      ?>
      <h2>Team</h2>
      Members of the junior lab:
      <ul>
        <li> Marc Lasson, in charge </li>
        <li> Guillaume Allais </li>
        <li> Marthe Bonamy </li>
        <li> Sylvain Dailler </li>
        <li> Jean-Marie Madiot </li>
        <li> Pierre-Marie Pédrot </li>
      </ul>

      Related members:
      <ul>
        <li><a href="http://sourceforge.net/project/memberlist.php?group_id=298939">Current team</a> (on Sourceforge)</li>
        <li><a href="http://graal.ens-lyon.fr/coquille/index.php?page=team">Former team</a> (COQUILLE project)</li>
      </ul>
      <?php
    } elseif ($lang == "fr") {
      ?>
      <h2>Équipe</h2>
      Membres du laboratoire junior :
      <ul>
        <li> Marc Lasson, responsable du laboratoire junior </li>
        <li> Guillaume Allais </li>
        <li> Marthe Bonamy </li>
        <li> Sylvain Dailler </li>
        <li> Jean-Marie Madiot </li>
        <li> Pierre-Marie Pédrot </li>
      </ul>

      Membres en rapport avec le projet :
      <ul>
        <li><a href="http://sourceforge.net/project/memberlist.php?group_id=298939">Équipe actuelle</a> (sur Sourceforge)</li>
        <li><a href="http://graal.ens-lyon.fr/coquille/index.php?page=team">Ancienne équipe</a> (projet COQUILLE)</li>
      </ul>
      <?php
    }
  }

  elseif($pagename == "results") {
    if ($lang == "en") {
      ?>
      <h2>A bunch of nice results</h2>
      <ul>
        <li>The uncountability of &#x211d;</li>
        <li>The reals axioms imply Markov principle</li>
        <li>Basel problem (<em>1+1/2²+1/3²+1/4²+...= &pi;²/6</em>)</li>
        <li>Stirling Formula (approximation for <em>n!</em>)</li>
      </ul>

      <h2>New libraries</h2>

      <ul>
        <li>Arithmetic</li>
        <li>Topology (Various typeclasses definitions)</li>
        <li>Clean libraries on sequences of reals or complexes</li>
        <li>Complexes' definition and collection of basic results</li>
        <li>Formalization of power series and their convergence radius</li>
      </ul>
      <?php
    } elseif ($lang == "fr") {
      ?>
      <h2>Quelques jolis résultats</h2>
      <ul>
        <li>&#x211d; est indénombrable</li>
        <li>L'axiomatique des réels implique le principe de Markov</li>
        <li>Problème de Bâle (<em>1+1/2²+1/3²+1/4²+...= &pi;²/6</em>)</li>
        <li>Formule de Stirling (approximation de <em>n!</em>)</li>
      </ul>

      <h2>De nouvelles bibliothèques</h2>

      <ul>
        <li>Arithmétique</li>
        <li>Topologie (définition de nombreuses typeclass de base, recherche de définitions les plus générales possibles)</li>
        <li>Bibliothèques ordonnées de résultats sur les suites et séries réelles et les suites complexes</li>
        <li>Définition et manipulation des complexes et des concepts de base</li>
        <li>Formalisation des séries entières et développements sur les rayons de convergence</li>
      </ul>
      <?php
    }
  }
  
  elseif($pagename == "publi") {
    if ($lang == "en" || $lang == "fr") {
      ?>
      <h2>Publications</h2>
      <ul>
        <li>G. Allais. <b>Coq with power series</b> (<a href="http://www.uc.pt/en/congressos/thedu/goalstopics/">THedu'11</a>) [<a href="files/thedu11.pdf">pdf</a> | slides]</li>
	<li>J-M Madiot, P-M. Pédrot. <b>Constructive axiomatic for the real numbers</b> (<a href="http://www.cs.ru.nl/~spitters/coqw.html">3rd Coq workshop</a>) [<a href="files/coqws11.pdf">pdf</a> | slides]</li>
	<li>G. Allais. <b>Using reflection to solve some differential equations</b> (<a href="http://www.cs.ru.nl/~spitters/coqw.html">3rd Coq workshop</a>) [<a href="files/itp11.pdf">pdf</a> | slides]</li>
      </ul>
      <?php
    }
  }
  
  elseif($pagename == "doc")
  {
    if ($doc) {
      include($doc);
    }
    else
    {
      if ($lang == "en") {
        ?>
        <h2>Links</h2>
        <ul>
          <li><a href="http://sourceforge.net/apps/mediawiki/coqtail/index.php?title=Main_Page">The project's Wiki</a></li>
          <li><a href="http://graal.ens-lyon.fr/coquille/coqdoc/">COQUILLE's project documentation</a></li>
        </ul>
        <?php
       //include('doc/index_en.html');
       include('doc/index.html');
     } else {
      ?>
        <h2>Liens</h2>
        <ul>
        <li><a href="http://sourceforge.net/apps/mediawiki/coqtail/index.php?title=Main_Page">Wiki du projet</a></li>
        <li><a href="http://graal.ens-lyon.fr/coquille/coqdoc/">Documentation de COQUILLE</a></li>
        </ul>
      <?php
      include ('doc/index.html');
     }
    }
  }
  include('foot.inc.php')
?>
