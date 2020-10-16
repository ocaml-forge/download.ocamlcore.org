SITE_ID=5183059a-4deb-49cb-b2d7-a4989b76c2ef

deploy:
	hugo
	netlify deploy --prod --dir=public --site=$(SITE_ID)

clean::
	 $(RM) -r public/

.PHONY: deploy
