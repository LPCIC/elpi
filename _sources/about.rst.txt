About
=====

This page is both an introspection and self documentation for this documentation stack.

Prerequisites
-------------

Before building this documentation, make sure to have ``sphinx`` installed:

.. code-block:: console

   pip install sphinx
   pip install in-place

To match the visuals used in the community (*e.g.* https://coq.inria.fr/distrib/current/refman/):

.. code-block:: console

   pip install sphinx-rtd-theme

On debian based systems, one can use the package manager:

.. code-block:: console

   apt install sphinx-doc
   apt install python3-sphinx-rtd-theme
   pip install in-place

Extensions
----------

This documentation can make use of the following plugins:

.. code-block:: python

   extensions = [
      'sphinx.ext.intersphinx',
      'sphinx.ext.githubpages'
   ]

Namely, ``intersphinx`` (https://www.sphinx-doc.org/en/master/usage/extensions/intersphinx.html) can generate links to the documentation of objects in external projects, either explicitly through the external role, or as a fallback resolution for any other cross-reference, and, ``githubpages`` (https://www.sphinx-doc.org/en/master/usage/extensions/githubpages.html#module-sphinx.ext.githubpages) which creates a ``.nojekyll`` file on generated HTML directory to publish the document on GitHub Pages.

Building
--------

``sphinx`` comes with its own helpers to build the documentation but are not meant to be used directly, see :doc:`playground` section for injection points.

Instead, use the ``doc-sphinx`` target of the source tree's root's ``Makefile`` to build the documentation:

.. code-block:: python

    make doc-build
 
Or, to build and publish the documentation to github pages:

.. code-block:: python

    make doc-publish
